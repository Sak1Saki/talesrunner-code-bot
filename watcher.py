#!/usr/bin/env python3
"""
TalesRunner live-code watcher.

Watches a YouTube channel's live stream, grabs a frame every few seconds,
reads on-screen text with OCR, picks out item codes and posts them to a
Discord webhook.

Commands:
  python watcher.py should-run          -> prints "yes"/"no" (live now, or inside schedule window)
  python watcher.py watch               -> watch live streams until deadline
  python watcher.py rescan              -> rescan finished streams (VOD) for codes that were missed
  python watcher.py vod URL [--post]    -> scan one past video (test). Prints codes; --post sends to Discord
  python watcher.py image FILE          -> OCR one image (test)
"""
import argparse
import glob
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from collections import Counter
from datetime import datetime, timedelta, timezone

from urllib.parse import urljoin

import requests

# ---------------------------------------------------------------- settings
CHANNEL = os.environ.get("CHANNEL_URL", "https://www.youtube.com/@thehof.talesrunner").rstrip("/")
# one or more webhook links (one per line, or separated by commas/spaces) → every room gets every post
WEBHOOKS = [w for w in re.split(r"[\s,]+", os.environ.get("DISCORD_WEBHOOK_URL", "")) if w.startswith("http")]
COOKIES = os.environ.get("YT_COOKIES_FILE", "")
INTERVAL = int(os.environ.get("FRAME_INTERVAL", "15"))      # seconds between frames
# "Is it live yet?" checks while waiting (each check is ~5 YouTube requests -> fewer checks, fewer 429s).
# The channel lives on a fixed schedule, so check often only around the scheduled start times.
LIVE_SLOTS = os.environ.get("LIVE_SLOTS", "14:00,16:30,19:00,21:30")  # scheduled start times (Thai time)
SLOT_BEFORE = int(os.environ.get("SLOT_BEFORE", "10"))     # minutes before a start time to check often
SLOT_AFTER = int(os.environ.get("SLOT_AFTER", "20"))       # minutes after (streamers often start late)
LIVE_CHECK_NEAR = int(os.environ.get("LIVE_CHECK_NEAR", "180"))  # seconds between checks near a start time
LIVE_CHECK = int(os.environ.get("LIVE_CHECK", "600"))           # seconds between checks at other times
# evidence needed before posting: same spelling read cleanly in 2 frames (30 s), or ~8 frames of guessed reads
THRESHOLD = float(os.environ.get("CODE_THRESHOLD", "4"))
MIN_SCORE = float(os.environ.get("OCR_MIN_SCORE", "0.85"))  # OCR confidence needed for a full-weight read
# Text that looks like a code but isn't (placeholder in the stream overlay template etc.).
# More can be added one per line in state/blocked.txt
BLOCKED = {"TONT4N2A2I2I", "ROSA4L8R4Z9I",
           "TOND0D8E2I6D"}  # 17/11/26: half of a sliced line misread (also removed from summaries)
REDEEM_URL = "https://member.thehof.gg/talesrunner/itemcode"  # "🎁 เติมโค้ด" link in each code post
STATE_DIR = os.environ.get("STATE_DIR", "state")
GIT_PERSIST = os.environ.get("GIT_PERSIST") == "1"
# Schedule window in Thai time (streams 14:00-~24:00). Outside it the watcher exits when nothing is live.
# Starts well before 14:00 because GitHub's timer often skips/delays runs (gaps of up to ~1.5 h seen).
WINDOW_START = os.environ.get("WINDOW_START", "12:30")
WINDOW_END = os.environ.get("WINDOW_END", "00:45")
ICT = timezone(timedelta(hours=7))

# ---------------------------------------------------------------- helpers


def log(*a):
    print(datetime.now(ICT).strftime("[%H:%M:%S]"), *a, flush=True)


def hms(sec):
    sec = max(0, int(sec))
    return f"{sec // 3600}:{sec % 3600 // 60:02d}:{sec % 60:02d}"


def _mins(hhmm):
    h, m = hhmm.split(":")
    return int(h) * 60 + int(m)


def in_window(now=None):
    now = now or datetime.now(ICT)
    m = now.hour * 60 + now.minute
    s, e = _mins(WINDOW_START), _mins(WINDOW_END)
    return s <= m <= e if s <= e else (m >= s or m <= e)


def next_check_delay(now=None):
    """Seconds to wait before the next "is it live yet?" check: LIVE_CHECK_NEAR around scheduled start
    times, LIVE_CHECK otherwise -- but never sleeping past the start of the next "check often" period."""
    now = now or datetime.now(ICT)
    m = now.hour * 60 + now.minute + now.second / 60
    wait = LIVE_CHECK
    for slot in filter(None, (s.strip() for s in LIVE_SLOTS.split(","))):
        s = _mins(slot)
        for day in (-1440, 0, 1440):  # periods that cross midnight
            lo, hi = s - SLOT_BEFORE + day, s + SLOT_AFTER + day
            if lo <= m < hi:
                return LIVE_CHECK_NEAR
            if m < lo:
                wait = min(wait, (lo - m) * 60)
    return max(5, int(wait))


def ffmpeg_exe():
    exe = shutil.which("ffmpeg")
    if exe:
        return exe
    import imageio_ffmpeg  # bundled static ffmpeg (works on Windows too)
    return imageio_ffmpeg.get_ffmpeg_exe()


def ytdlp_cmd(need_ffmpeg=False):
    cmd = [sys.executable, "-m", "yt_dlp", "--no-warnings", "--no-progress"]
    if need_ffmpeg:
        cmd += ["--ffmpeg-location", ffmpeg_exe()]
    if not shutil.which("deno") and shutil.which("node"):
        cmd += ["--js-runtimes", "node"]
    if COOKIES and os.path.exists(COOKIES) and os.path.getsize(COOKIES) > 0:
        cmd += ["--cookies", COOKIES]
    return cmd


# ---------------------------------------------------------------- code detection
# Codes seen so far: VASE9R7K1J6M, ZEAL4C5Z9V2H, COMB8N1Q3M7T
#   = 4 letters, then digit/letter alternating 4 times (12 chars).
CODE_RE = re.compile(r"[A-Z]{4}(?:[0-9][A-Z]){4}")
TO_DIGIT = str.maketrans("OQDILZSBGTA", "00011258674")
TO_LETTER = str.maketrans("01524867", "OISZABGT")


def _fix(window):
    """Correct common OCR mix-ups using the known position pattern."""
    out = []
    for i, ch in enumerate(window):
        if i < 4 or i % 2 == 1:
            ch = ch.translate(TO_LETTER)
            if not ch.isalpha():
                return None
        else:
            ch = ch.translate(TO_DIGIT)
            if not ch.isdigit():
                return None
        out.append(ch)
    return "".join(out)


def extract_codes(lines):
    """Return {code: (weight, source text, sure)} for one frame.
    Weight: confident OCR, code standing on its own anywhere on screen (label or not) = 2;
    low-confidence or buried inside other text = 0.5;
    needed letter/digit correction = 1 next to the word CODE, 0.25 otherwise.
    sure: OCR was confident (>= MIN_SCORE) about the text AND it was the code as-is, or a 12-character
    word on its own that needed at most 1 letter/digit swap (O->0 etc.). Ordinary words that only turn into
    a code after several swaps (LOADINGPLEASE -> LOAD1N6P1E4S) are never "sure", so they are never posted."""
    found = {}

    def add(c, w, src, is_sure):
        old = found.get(c, (0, "", False))
        sure_now = old[2] or is_sure
        found[c] = (w, src, sure_now) if w > old[0] else (old[0], old[1], sure_now)

    for item in lines:
        line, score = item if isinstance(item, tuple) else (item, 1.0)
        up = line.upper()
        sure = score >= MIN_SCORE   # OCR is confident about this text box (Thai text read as junk scores low)
        ctx = "CODE" in re.sub(r"[^A-Z]", "", up.replace("0", "O"))
        src = f"{line} ({score:.2f})"
        # exact matches, also with spaces removed (OCR sometimes splits a code)
        for text in (up, re.sub(r"\s+", "", up)):
            for tok in re.split(r"[^A-Z0-9]+", text):
                for c in CODE_RE.findall(tok):
                    # full weight only when the code stands on its own (or right after "CODE" / "CODE1")
                    clean = tok == c or re.fullmatch(r"C[O0]DE\d?" + c, tok)
                    add(c, 2 if clean and sure else 0.5, src, sure)
        # fuzzy: tokens about the length of a code
        for tok in re.split(r"[^A-Z0-9]+", up):
            if 12 <= len(tok) <= 14 and not CODE_RE.search(tok):
                for i in range(len(tok) - 11):
                    c = _fix(tok[i:i + 12])
                    if c:
                        swaps = sum(a != b for a, b in zip(tok[i:i + 12], c))
                        one_swap = sure and len(tok) == 12 and swaps <= 1  # e.g. C0MB8N1Q3M7T -> COMB8N1Q3M7T
                        # a confident code-shaped word with one swap counts like a read next to "CODE"
                        # (not every streamer labels codes), so it is posted after ~1 minute, not ~4
                        add(c, 1 if sure and (ctx or one_swap) else 0.25, src, one_swap)
    return found


_blocked_cache = None


def blocked():
    global _blocked_cache
    if _blocked_cache is None:
        _blocked_cache = set(BLOCKED)
        try:
            with open(os.path.join(STATE_DIR, "blocked.txt"), encoding="utf-8") as f:
                _blocked_cache |= {l.strip().upper() for l in f if l.strip() and not l.startswith("#")}
        except OSError:
            pass
    return _blocked_cache


def hamming(a, b):
    return sum(x != y for x, y in zip(a, b)) + abs(len(a) - len(b))


_ocr = None


def _ocr_img(img, cut_top=False, cut_bottom=False):
    """OCR one image. cut_top/cut_bottom: that edge was cut out of a bigger frame, so text touching it
    may be sliced in half (half a line reads as a fake code) -> drop it; the overlapping band has it whole."""
    global _ocr
    if _ocr is None:
        from rapidocr_onnxruntime import RapidOCR
        _ocr = RapidOCR()
    result, _ = _ocr(img)
    h, out = img.shape[0], []
    for box, text, score in result or []:
        ys = [p[1] for p in box]
        if (cut_top and min(ys) <= 4) or (cut_bottom and max(ys) >= h - 5):
            continue
        out.append((text, float(score)))
    return out


# horizontal bands read again at 2x so small text is clear, wherever the stream layout puts the codes.
# They overlap by 10% of the frame, so any line cut by one band's edge is whole in the next band.
BANDS = ((0.0, 0.4), (0.3, 0.7), (0.6, 1.0))


def ocr_lines(path):
    """OCR the whole frame, plus 2x-enlarged overlapping bands."""
    import cv2
    img = cv2.imread(path)
    if img is None:
        return []
    h = img.shape[0]
    lines = _ocr_img(img)
    for y0, y1 in BANDS:
        crop = img[int(h * y0):int(h * y1), :]
        lines += _ocr_img(cv2.resize(crop, None, fx=2, fy=2, interpolation=cv2.INTER_CUBIC),
                          cut_top=y0 > 0, cut_bottom=y1 < 1)
    return lines


# ---------------------------------------------------------------- state (one small file per item -> no git conflicts)


def _load(path, default=None):
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    except (OSError, ValueError):
        return default


def _save(path, data):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=1)


def code_file(code):
    return os.path.join(STATE_DIR, "codes", f"{code}.json")


def video_file(vid):
    return os.path.join(STATE_DIR, "videos", f"{vid}.json")


def persist(msg):
    if not GIT_PERSIST:
        return
    try:
        subprocess.run(["git", "add", STATE_DIR], check=True)
        if subprocess.run(["git", "diff", "--cached", "--quiet"]).returncode == 0:
            return
        subprocess.run(["git", "commit", "-q", "-m", msg], check=True)
        for _ in range(5):
            subprocess.run(["git", "pull", "-q", "--rebase", "-X", "theirs"])
            if subprocess.run(["git", "push", "-q"]).returncode == 0:
                return
            time.sleep(5)
        log("WARN: could not push state")
    except Exception as e:  # never let state saving kill the watcher
        log("WARN: persist failed:", e)


# ---------------------------------------------------------------- discord


def discord(content=None, embed=None, image=None):
    if not WEBHOOKS:
        log("[discord-dry-run]", content or "", json.dumps(embed, ensure_ascii=False) if embed else "")
        return
    payload = {"content": content, "allowed_mentions": {"parse": []}}
    if embed:
        if image:
            embed["image"] = {"url": "attachment://frame.jpg"}
        payload["embeds"] = [embed]
    for n, hook in enumerate(WEBHOOKS, 1):
        for _ in range(4):
            try:
                if image and os.path.exists(image):
                    with open(image, "rb") as f:
                        r = requests.post(hook, data={"payload_json": json.dumps(payload)},
                                          files={"files[0]": ("frame.jpg", f, "image/jpeg")}, timeout=30)
                else:
                    r = requests.post(hook, json=payload, timeout=30)
                if r.status_code == 429:
                    time.sleep(float(r.json().get("retry_after", 2)) + 0.5)
                    continue
                if r.status_code in (401, 403, 404):
                    log(f"discord: webhook #{n} was deleted or is wrong (HTTP {r.status_code}), skipping it")
                    break
                r.raise_for_status()
                break
            except Exception as e:
                log(f"discord error (webhook #{n}):", type(e).__name__)  # never log the URL itself
                time.sleep(3)


_warned_block = False


def recovered():
    """After a ⚠️ warning, say so as soon as the video can be read again."""
    global _warned_block
    if _warned_block:
        _warned_block = False
        discord("✅ บอทกลับมาดูไลฟ์ได้แล้ว ไม่ต้องทำอะไรค่ะ")


def is_block(err):
    return any(s in err for s in ("Sign in to confirm", "HTTP Error 429", "not a bot"))


def key_error(err):
    """The lines that explain the failure (yt-dlp ERROR lines first), not just the tail."""
    lines = [l for l in err.splitlines() if l.strip()]
    important = [l for l in lines if "ERROR" in l]
    return "\n".join((important[-2:] + lines[-2:]) if important else lines[-4:])[-500:]


def warn_blocked(err):
    global _warned_block
    if _warned_block:
        return
    _warned_block = True
    if is_block(err):
        msg = ("⚠️ บอทเข้า YouTube ไม่ได้ (YouTube บล็อกเซิร์ฟเวอร์ของ GitHub) — "
               "ดูวิธีแก้ในหัวข้อ \"ถ้า YouTube บล็อก\" ใน README")
    else:
        msg = "⚠️ ดึงภาพไลฟ์ไม่ได้มาหลายนาทีแล้ว บอทกำลังลองใหม่เรื่อยๆ"
    discord(msg + "\n```" + key_error(err) + "```")


# ---------------------------------------------------------------- youtube


def _ytdlp_json(args):
    """Run yt-dlp; a hang (YouTube very slow) counts as a failed attempt instead of crashing the bot."""
    try:
        return subprocess.run(ytdlp_cmd() + args, capture_output=True, text=True,
                              encoding="utf-8", errors="replace", timeout=120)
    except subprocess.TimeoutExpired:
        return subprocess.CompletedProcess(args, 1, "", "yt-dlp timed out (YouTube did not answer in 2 minutes)")


def video_info(url):
    r = _ytdlp_json(["-J", "--skip-download", "--ignore-no-formats-error", url])
    if r.returncode != 0:
        err = r.stderr.strip()
        if "Sign in to confirm" in err or "HTTP Error 429" in err:
            warn_blocked(err)
        if "not currently live" not in err and "will begin" not in err:
            log("yt-dlp:", err[-300:])
        return None
    try:
        return json.loads(r.stdout)
    except ValueError:
        return None


def get_live():
    info = video_info(CHANNEL + "/live")
    if info and info.get("live_status") == "is_live":
        return info
    return None


# video formats to try; after a failed start the next attempt uses the next one
FORMATS = ["bv*[height<=1080]/b", "b[height<=720]/bv*[height<=720]/b"]


def live_source(url, attempt=0):
    """Ask YouTube once for the live stream's video link (HLS playlist; valid for hours).
    Returns ({"url", "headers", "at"}, "") or (None, error text)."""
    r = _ytdlp_json(["-J", "-f", FORMATS[attempt % len(FORMATS)], url])
    try:
        info = json.loads(r.stdout) if r.returncode == 0 else {}
    except ValueError:
        info = {}
    if info and info.get("live_status") != "is_live":
        # the stream is over: its link now points at the recording, which grab_live must not read
        return None, f"stream is not live any more ({info.get('live_status')})"
    fmt = info if info.get("url") else (info.get("requested_formats") or [{}])[0]
    if not fmt.get("url"):
        return None, r.stderr.strip()[-3000:] or "no stream link"
    return {"url": fmt["url"], "headers": fmt.get("http_headers") or {}, "at": time.time()}, ""


JPEG_VF = "scale=-2:'min(1080,ih)':out_range=full,format=yuvj420p"


def start_pipeline(url, outdir, errpath, attempt=0):
    """Finished videos: yt-dlp -> ffmpeg, writing one JPEG every INTERVAL seconds of video."""
    errf = open(errpath, "wb")
    y = subprocess.Popen(ytdlp_cmd(need_ffmpeg=True) + ["-f", FORMATS[attempt % len(FORMATS)], "-o", "-", url],
                         stdout=subprocess.PIPE, stderr=errf)
    # skip broken packets instead of dying on them, and convert every frame to a fixed full-range
    # JPEG pixel format so the JPEG encoder never rejects a frame (error -22 "Invalid argument")
    f = subprocess.Popen([ffmpeg_exe(), "-loglevel", "error", "-fflags", "+discardcorrupt+genpts",
                          "-err_detect", "ignore_err", "-i", "pipe:0", "-map", "0:v:0",
                          "-vf", f"fps=1/{INTERVAL}," + JPEG_VF, "-strict", "unofficial", "-q:v", "3",
                          os.path.join(outdir, "f_%06d.jpg")], stdin=y.stdout, stderr=errf)
    y.stdout.close()
    errf.close()
    return y, f


# ---------------------------------------------------------------- live grabber
# YouTube answers "429 Too Many Requests" to GitHub's servers when the live playlist is re-read every
# few seconds (what ffmpeg/yt-dlp do), and ffmpeg then just stops. Instead, every INTERVAL seconds we
# read the playlist once, download only the newest segment and take one frame from it:
# ~2 small requests per 15 s, and on 429 we simply wait and try again.


class LinkExpired(Exception):
    pass


def _hls_get(sess, url, timeout=20):
    r = sess.get(url, timeout=timeout)
    if r.status_code in (403, 404, 410):
        raise LinkExpired(f"HTTP {r.status_code}")
    if r.status_code != 200:
        raise RuntimeError(f"HTTP {r.status_code} {r.reason}")  # never include the URL (it is long + signed)
    return r


def _pick_variant(text, base):
    """Master playlist -> best variant up to 1080p."""
    best, lines = None, text.splitlines()
    for i, l in enumerate(lines):
        if l.startswith("#EXT-X-STREAM-INF") and i + 1 < len(lines):
            m = re.search(r"RESOLUTION=\d+x(\d+)", l)
            h = int(m.group(1)) if m else 0
            if h <= 1080 and (best is None or h > best[0]):
                best = (h, urljoin(base, lines[i + 1].strip()))
    if not best:
        raise RuntimeError("no video in master playlist")
    return best[1]


def _parse_media(text, base):
    m = re.search(r"#EXT-X-MEDIA-SEQUENCE:(\d+)", text)
    seq = int(m.group(1)) if m else 0
    segs = [urljoin(base, l.strip()) for l in text.splitlines() if l.strip() and not l.startswith("#")]
    m = re.search(r'#EXT-X-MAP:.*URI="([^"]+)"', text)
    return seq + len(segs) - 1, (segs[-1] if segs else None), (urljoin(base, m.group(1)) if m else None)


def grab_live(scan, src, deadline):
    """Returns "deadline", "ended", "stalled" (no new video), "expired" (get a new link) or "failed"."""
    sess = requests.Session()
    sess.headers.update(src["headers"])
    pl_url, last_n, init, errs, last_ok = src["url"], None, None, 0, time.time()
    tmp = tempfile.mkdtemp(prefix="live_")
    seg_path = os.path.join(tmp, "seg")
    try:
        while time.time() < deadline:
            t0 = time.time()
            try:
                text = _hls_get(sess, pl_url).text
                if "#EXT-X-STREAM-INF" in text:
                    pl_url = _pick_variant(text, pl_url)
                    continue
                n, seg, init_url = _parse_media(text, pl_url)
                if seg is None:
                    if "#EXT-X-ENDLIST" in text:
                        return "ended"
                    raise RuntimeError("empty playlist")
                if n == last_n:
                    if time.time() - last_ok > 180:
                        return "stalled"  # no new video for 3 minutes: stream probably ended -> caller checks
                    if "#EXT-X-ENDLIST" in text:
                        return "ended"
                else:
                    if init_url and init is None:
                        init = _hls_get(sess, init_url).content
                    for i in range(4):  # a refused segment usually works a few seconds later
                        try:
                            data = _hls_get(sess, seg, timeout=40).content
                            break
                        except RuntimeError:
                            if i == 3:
                                raise
                            time.sleep(3 * (i + 1))
                    with open(seg_path, "wb") as f:
                        f.write((init or b"") + data)
                    path = os.path.join(tmp, f"f_{n % 1000000:06d}.jpg")
                    r = subprocess.run([ffmpeg_exe(), "-loglevel", "error", "-y", "-err_detect", "ignore_err",
                                        "-i", seg_path, "-map", "0:v:0", "-frames:v", "1", "-vf", JPEG_VF,
                                        "-strict", "unofficial", "-q:v", "3", path],
                                       capture_output=True, text=True, errors="replace", timeout=60)
                    if not os.path.exists(path):
                        raise RuntimeError("ffmpeg: " + (r.stderr.strip()[-300:] or "no frame"))
                    last_n, errs, last_ok = n, 0, time.time()
                    scan.frame(path, time.time() - scan.start_ts)
                    scan.frames += 1
                    recovered()
                    if scan.frames % 40 == 0:
                        log(f"{scan.frames} frames read, top readings: {scan.counts.most_common(6)}")
                    os.remove(path)
            except LinkExpired as e:
                scan.err = f"stream link stopped working ({e})"
                log(scan.err)
                return "expired"
            except Exception as e:
                errs += 1
                scan.err = f"{type(e).__name__}: {e}"[:500]
                log(f"live read error ({errs} in a row): {scan.err}")
                if time.time() - last_ok > 600:  # ~10 minutes without a single frame
                    warn_blocked(scan.err)
                if errs >= 8:
                    return "failed"
                time.sleep(min(10 * errs, 60))  # 429 etc.: back off, then try again
                continue
            time.sleep(max(1.0, INTERVAL - (time.time() - t0)))
        return "deadline"
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def stop(*procs):
    procs = [p for p in procs if p]
    for p in procs:
        if p.poll() is None:
            p.terminate()
    for p in procs:
        try:
            p.wait(timeout=10)
        except subprocess.TimeoutExpired:
            p.kill()


# ---------------------------------------------------------------- scanning


class Scan:
    """Tracks code sightings for one video."""

    def __init__(self, info, mode, post=True):
        self.vid = info["id"]
        self.title = info.get("title") or self.vid
        self.start_ts = info.get("release_timestamp") or info.get("timestamp") or time.time()
        self.mode = mode            # "live" | "rescan" | "test"
        self.post = post
        self.counts = Counter()     # weighted sightings per exact spelling
        self.clusters = []          # [{"v": Counter, "posted": code|None}] similar spellings grouped
        self.src = {}               # last OCR text each code was read from (for debugging)
        self.sure = set()           # spellings read at least once with confident OCR
        self.frames = 0
        self.err = ""
        self.state =_load(video_file(self.vid)) or {
            "id": self.vid, "title": self.title, "start": self.start_ts,
            "codes": [], "ended": False, "rescanned": False}

    def frame(self, path, offset):
        try:
            lines = ocr_lines(path)
        except Exception as e:
            log("ocr error:", e)
            return
        for code, (w, src, sure) in extract_codes(lines).items():
            if code in blocked():
                continue
            self.counts[code] += w
            self.src[code] = src
            if sure:
                self.sure.add(code)
            cl = next((c for c in self.clusters if any(hamming(code, k) <= 2 for k in c["v"])), None)
            if cl is None:
                cl = {"v": Counter(), "posted": None}
                self.clusters.append(cl)
            cl["v"][code] += w
            self.decide(cl, path, offset)

    def decide(self, cl, path, offset):
        """Post the most-seen spelling once there is enough evidence; correct it if another spelling wins later."""
        best, best_n = cl["v"].most_common(1)[0]
        # never post a spelling that OCR was never confident about, however often it was seen
        # (e.g. half of a sliced line read again and again while the code stays on screen)
        if best_n < THRESHOLD or best not in self.sure:
            return
        if cl["posted"] is None:
            cl["posted"] = best
            self.publish(best, path, offset)
        elif best != cl["posted"] and best_n >= cl["v"][cl["posted"]] + THRESHOLD:
            old, cl["posted"] = cl["posted"], best
            self.publish(best, path, offset, wrong=old)

    def _known(self, code):
        """Already posted before (same code or a near-identical misread of it)?"""
        if os.path.exists(code_file(code)):
            return True
        for p in glob.glob(os.path.join(STATE_DIR, "codes", "*.json")):
            if hamming(code, os.path.basename(p)[:-5]) <= 1:
                return True
        return False

    def publish(self, code, path, offset, wrong=None):
        when = datetime.fromtimestamp(self.start_ts + offset, ICT)
        log(f"CODE {code}  at {when:%H:%M} (+{hms(offset)})" + (f"  (correcting {wrong})" if wrong else ""))
        label = {"live": "🎁 โค้ดใหม่", "rescan": "🔁 โค้ดที่ตกหล่น (สแกนย้อนหลัง)", "test": "🧪 ทดสอบ"}[self.mode]
        if wrong:
            label = f"✏️ แก้ไข: โค้ดที่ส่งไปก่อนหน้า `{wrong}` อ่านผิด ที่ถูกคือ"
        if self.mode == "test":
            if self.post:
                self.send(code, path, offset, when, label + f"\n-# อ่านจาก: {self.src.get(code, '')[:120]}")
            return
        if wrong and wrong in self.state["codes"]:
            self.state["codes"].remove(wrong)
            try:
                os.remove(code_file(wrong))
            except OSError:
                pass
        if code not in self.state["codes"]:
            self.state["codes"].append(code)
            _save(video_file(self.vid), self.state)
        if not wrong and self._known(code):
            return  # already posted (maybe from another stream)
        _save(code_file(code), {"code": code, "video": self.vid, "title": self.title,
                                "time": when.isoformat(), "offset": int(offset)})
        self.send(code, path, offset, when, label)
        persist(f"code {code}")

    def send(self, code, path, offset, when, label):
        link = f"https://youtu.be/{self.vid}?t={int(offset)}"
        # live posts arrive within a minute, so Discord's own timestamp already shows the time;
        # rescan/test posts come later, so they keep when the code was on screen
        stamp = "" if self.mode == "live" else f"🕒 {when:%d/%m %H:%M} น. · "
        discord(content=f"{label}\n```\n{code}\n```",  # code box: one-click copy button on a computer
                embed={"description": f"{stamp}นาทีที่ {hms(offset)} · [▶️ ดูช่วงนี้]({link})"
                                      f" · [🎁 เติมโค้ด]({REDEEM_URL})",
                       "color": 0xF5A623},
                image=path)
        # the code goes alone in its own message, so on a phone "long-press → Copy Text" copies just the code
        discord(content=code)


def run_frames(url, scan, offset_fn, deadline, attempt=0):
    """Run the pipeline until the video ends or deadline. Returns True if it ended by itself."""
    tmp = tempfile.mkdtemp(prefix="frames_")
    errpath = tmp + "_err.log"
    y, f = start_pipeline(url, tmp, errpath, attempt)
    ended = False
    scan.frames = 0
    try:
        while True:
            done = f.poll() is not None
            files = sorted(glob.glob(os.path.join(tmp, "f_*.jpg")))
            if not done:
                files = files[:-1]  # newest may still be being written
            for p in files:
                n = int(os.path.basename(p)[2:8])
                scan.frame(p, offset_fn(n, p))
                scan.frames += 1
                if scan.frames == 1:
                    recovered()
                if scan.frames % 40 == 0:
                    log(f"{scan.frames} frames read, top readings: {scan.counts.most_common(6)}")
                os.remove(p)
            if done:
                ended = True
                break
            if time.time() > deadline:
                break
            time.sleep(2)
    finally:
        stop(f, y)
        shutil.rmtree(tmp, ignore_errors=True)
        try:
            with open(errpath, encoding="utf-8", errors="replace") as ef:
                scan.err = "\n".join(l for l in ef.read().splitlines() if "[download]" not in l)[-3000:]
            os.remove(errpath)
        except OSError:
            scan.err = ""
    if scan.frames == 0:
        log("NO FRAMES. downloader output:\n" + scan.err)
        # live mode retries by itself and only warns after repeated failures (see watch_stream)
        if scan.mode != "live" and is_block(scan.err):
            warn_blocked(scan.err)
    return ended


def summary(scan):
    summary_post(scan.state, scan.title)


def summary_post(state, title):
    # drop junk that was saved before it was blocked (e.g. by a run that started with older code)
    codes = [c for c in state["codes"] if c not in blocked()]
    body = "\n".join(f"`{c}`" for c in codes) if codes else "ไม่พบโค้ดในไลฟ์นี้"
    discord(embed={"title": "📋 สรุปโค้ดจากไลฟ์", "color": 0x5865F2,
                   "description": f"**{title}**\nhttps://youtu.be/{state['id']}\n\n{body}"})


def close_unseen_ends(skip_id=None):
    """A live that ended while no run was watching it (run cancelled, or between two runs) never got its
    summary nor the "ended" mark the nightly rescan needs. Find those and finish them now."""
    for path in sorted(glob.glob(os.path.join(STATE_DIR, "videos", "*.json"))):
        st = _load(path)
        if not st or st.get("ended") or st.get("id") == skip_id:
            continue
        info = video_info(f"https://www.youtube.com/watch?v={st['id']}")
        if not info or info.get("live_status") == "is_live":
            continue  # still on (or YouTube did not answer): leave it for the watcher / next time
        st["ended"] = True
        _save(path, st)
        log("live ended while not watched -> closing", st["id"])
        if time.time() - float(st.get("start") or 0) < 24 * 3600:  # don't post summaries of old lives
            summary_post(st, st.get("title") or st["id"])
        persist(f"ended {st['id']}")


def watch_stream(info, deadline):
    url = f"https://www.youtube.com/watch?v={info['id']}"
    scan = Scan(info, "live")
    if not os.path.exists(video_file(scan.vid)):
        _save(video_file(scan.vid), scan.state)
        discord(embed={"title": "🔴 เริ่มไลฟ์แล้ว — บอทกำลังดูโค้ดให้", "color": 0xE02B2B,
                       "description": f"**{scan.title}**\nhttps://youtu.be/{scan.vid}"})
        persist(f"live {scan.vid}")
    log("watching", scan.vid, scan.title)
    fails = 0
    while time.time() < deadline:
        src, err = live_source(url, fails)  # one YouTube request round; the link then lasts for hours
        before = scan.frames
        if src:
            res = grab_live(scan, src, deadline)
            if res == "deadline":
                return  # out of time; next run continues this stream
        else:
            res, scan.err = "nolink", err
            log("could not get the stream link: " + key_error(err))
        fails = 0 if scan.frames > before else fails + 1
        if fails == (3 if is_block(scan.err) else 6):
            warn_blocked(scan.err)
        if "not live any more" in scan.err:
            break
        # whatever stopped the reading, check the stream is still on (and that no new one replaced it)
        # before going on -- otherwise the bot keeps retrying a finished stream and misses the next one
        if res != "expired" or fails:
            again = get_live()
            if not again or again["id"] != scan.vid:
                break  # stream is over
        limited = any(s in scan.err for s in ("429", "Too Many Requests", "No video formats"))
        time.sleep(2 if fails == 0 else min((60 if limited else 20) * fails, 300))
        log(f"getting a fresh stream link ({res})")
    else:
        return
    scan.state["ended"] = True
    _save(video_file(scan.vid), scan.state)
    summary(scan)
    persist(f"ended {scan.vid}")


def scan_vod(info, mode, post, deadline):
    url = f"https://www.youtube.com/watch?v={info['id']}"
    scan = Scan(info, mode, post)
    log("scanning VOD", scan.vid, scan.title, f"({hms(info.get('duration') or 0)})")
    ok = run_frames(url, scan, lambda n, p: (n - 1) * INTERVAL, deadline)
    return scan, ok


# ---------------------------------------------------------------- commands


def cmd_should_run():
    print("yes" if in_window() or get_live() else "no")


def cmd_watch(max_minutes):
    deadline = time.time() + max_minutes * 60
    closed = False
    while time.time() < deadline - 60:
        try:
            info = get_live()
            if not closed:  # once per run: finish lives that ended while nobody was watching
                closed = True  # marked first: if it fails, skip it (next run retries) instead of looping
                close_unseen_ends(skip_id=info["id"] if info else None)
            if info:
                watch_stream(info, deadline - 60)
                continue
        except Exception as e:  # never let one unexpected error stop the whole run
            log("ERROR (continuing):", type(e).__name__, e)
            time.sleep(30)
            continue
        if not in_window():
            log("nothing live and outside schedule window -> exit")
            break
        # often near scheduled start times, rarely otherwise; never sleep past the end of this run
        time.sleep(max(1, min(next_check_delay(), deadline - 60 - time.time())))
    else:
        try:
            more = in_window() or get_live()
        except Exception:
            more = True  # unsure -> better to start the next run than to stop watching
        if more:
            open(".continue", "w").close()  # tells the workflow to start the next run right away
    log("watch finished")


def cmd_rescan(max_minutes):
    deadline = time.time() + max_minutes * 60
    close_unseen_ends(skip_id=(get_live() or {}).get("id"))
    for path in sorted(glob.glob(os.path.join(STATE_DIR, "videos", "*.json"))):
        st = _load(path)
        if not st or st.get("rescanned") or not st.get("ended"):
            continue
        if time.time() > deadline - 600:
            break
        info = video_info(f"https://www.youtube.com/watch?v={st['id']}")
        if not info or info.get("live_status") not in ("was_live", "not_live", None):
            log("VOD not ready:", st["id"])
            continue
        scan, ok = scan_vod(info, "rescan", True, deadline)
        # the download can stop early (429, cut connection) and still look "finished":
        # only count it as rescanned when frames covering ~all of the video were really read
        need = 0.9 * (info.get("duration") or 0) / INTERVAL
        if ok and scan.frames > 0 and scan.frames >= need:
            scan.state["rescanned"] = True
            _save(video_file(scan.vid), scan.state)
            persist(f"rescanned {scan.vid}")


def cmd_vod(url, post):
    if post:
        discord("🧪 เริ่มทดสอบ — บอทกำลังดูไลฟ์เก่า อาจใช้เวลา 20–40 นาที")
    info = video_info(url)
    if not info:
        if post:
            discord("❌ ทดสอบไม่สำเร็จ: เปิดข้อมูลคลิปจาก YouTube ไม่ได้")
        sys.exit("cannot read video (see error above)")
    scan, _ = scan_vod(info, "test", post, time.time() + 5 * 3600)
    print(f"\n=== {scan.frames} frames read — codes found ===")
    lines = []
    for cl in sorted(scan.clusters, key=lambda c: -sum(c["v"].values())):
        print(dict(cl["v"]), "-> posted:", cl["posted"])
        if cl["posted"]:
            lines.append(f"✅ `{cl['posted']}`")
    ignored = sum(1 for cl in scan.clusters if not cl["posted"])
    if ignored:
        lines.append(f"(ตัดทิ้ง {ignored} อันที่น่าจะอ่านผิด/เห็นน้อยเกินไป)")
    if scan.frames == 0:
        if post:
            discord("❌ ทดสอบไม่สำเร็จ: โหลดวิดีโอไม่ได้\n```" + (scan.err or "no output")[-1500:] + "```")
        sys.exit("no frames were read — download failed (see output above)")
    if post:
        discord(f"🧪 ทดสอบเสร็จ อ่านไป {scan.frames} ภาพ\n" + ("\n".join(lines) if lines else "ไม่เจอโค้ดเลย"))


def cmd_image(path):
    lines = ocr_lines(path)
    print("OCR lines:")
    for l in lines:
        print("  ", l)
    print("codes:", sorted(extract_codes(lines)) or "(none)")


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("should-run")
    w = sub.add_parser("watch")
    w.add_argument("--max-minutes", type=int, default=335)
    r = sub.add_parser("rescan")
    r.add_argument("--max-minutes", type=int, default=335)
    v = sub.add_parser("vod")
    v.add_argument("url")
    v.add_argument("--post", action="store_true")
    i = sub.add_parser("image")
    i.add_argument("file")
    a = ap.parse_args()
    if a.cmd == "should-run":
        cmd_should_run()
    elif a.cmd == "watch":
        cmd_watch(a.max_minutes)
    elif a.cmd == "rescan":
        cmd_rescan(a.max_minutes)
    elif a.cmd == "vod":
        cmd_vod(a.url, a.post)
    elif a.cmd == "image":
        cmd_image(a.file)


if __name__ == "__main__":
    main()
