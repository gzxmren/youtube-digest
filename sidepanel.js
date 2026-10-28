/**
 * SIDE PANEL LOGIC
 *
 * Handles the UI for YouTube Digest: video detection, transcript analysis,
 * rendering results, and export features.
 */

const DEBUG = false;
const debugLog = (...args) => {
  if (DEBUG) console.log(...args);
};

// ============================================================
// STATE
// ============================================================

let currentVideoId = null;
let currentVideoUrl = null;
let currentAnalysis = null;
let currentTranscript = null;
let currentTranscriptText = null; // Plain text (for display/export)
let currentTranscriptTimestamped = null; // With timestamps for AI analysis
let currentTranscriptLanguage = null;
let currentVideoTitle = "";
let currentChannelName = "";
let currentVideoDescription = "";
let currentVideoDuration = 0;
let isAnalysisLoading = false; // Track if analysis is in progress
let youtubeTabId = null; // Store the YouTube tab ID for reliable messaging
let errorAction = null;
// When true, one panel stays open and follows the user across tabs instead of
// closing itself whenever the front tab is not a YouTube video page.
let keepPanelOpenAcrossTabs = true;

// --- Translation state ---
// The universal language control supports original content, Chinese, and an
// aligned bilingual view across Transcript, Overview, and Notes.
let currentTranscriptMode = "original";
const DISPLAY_LANGUAGE_MODE_KEY = "ytd_display_language_modes_by_video";
const DISPLAY_LANGUAGE_MODES = new Set(["original", "zh", "bilingual"]);
let translationGeneration = 0; // Invalidates responses from older UI modes/videos.
let translationWorkCount = 0;
let transcriptScrollObserver = null;
// Stable keys include the video, source mode, language, and semantic segment ID.
let transcriptParagraphCache = new Map();
let interfaceTranslationCache = new Map();
let interfaceTranslationInFlight = new Set();
let interfaceTranslationFailures = new Set();
let currentNotes = [];
let currentNotesFilterVideoId = null;
const TRANSLATION_MESSAGE_TIMEOUT_MS = 130_000;
const TRANSLATION_BATCH_SIZE = 3;

// --- Transcript search state ---
// Matches point to visible marks in the active transcript language mode.
// Search navigation only scrolls the panel. It does not seek the video.
let transcriptSearchMatches = [];
let transcriptSearchIndex = -1;

/**
 * Prevent a stopped service worker or dead message channel from leaving the
 * transcript queue stuck forever. The underlying Chrome message cannot be
 * cancelled, so settled guards deliberately ignore any late response.
 */
function sendTranslationMessage(message) {
  return new Promise((resolve, reject) => {
    let settled = false;
    let timeoutId;
    const finish = (callback, value) => {
      if (settled) return;
      settled = true;
      clearTimeout(timeoutId);
      callback(value);
    };

    timeoutId = setTimeout(() => {
      finish(
        reject,
        new Error(
          "Translation request timed out after 130 seconds. Please Retry.",
        ),
      );
    }, TRANSLATION_MESSAGE_TIMEOUT_MS);

    let messagePromise;
    try {
      messagePromise = chrome.runtime.sendMessage(message);
    } catch (error) {
      finish(reject, error);
      return;
    }

    Promise.resolve(messagePromise).then(
      (result) => finish(resolve, result),
      (error) => finish(reject, error),
    );
  });
}

// --- Auto-scroll state (follow video playback in transcript) ---
let autoScrollEnabled = true; // True = scroll transcript to follow video playback
let autoScrollInterval = null; // setInterval ID for polling video time
let lastAutoScrollTime = 0; // Timestamp of last programmatic scroll (ignores scroll events within 1s)

// --- Transcript reading position state ---
// Session storage survives a side panel close but clears when Chrome closes.
const TRANSCRIPT_VIEW_STATE_KEY = "ytd_transcript_view_state";
let pendingTranscriptViewState = null;
let transcriptViewStateSaveTimer = null;
let isRestoringTranscriptView = false;
let selectionActionsController = null;
let lastTranscriptScrollTop = 0;

// ============================================================
// TRANSCRIPT GROUPING
// ============================================================

const TRANSCRIPT_SEGMENT_LIMITS = Object.freeze({
  minChars: 60,
  idealChars: 180,
  maxChars: 320,
  maxSeconds: 20,
});

function normalizeCaptionText(text) {
  return String(text || "")
    .replace(/\s+/g, " ")
    .replace(/([\u3400-\u9fff])\s+([\u3400-\u9fff])/g, "$1$2")
    .replace(/([，。；：！？])\s+(?=[\u3400-\u9fff])/g, "$1")
    .replace(/\s+([,.;:!?，。；：！？])/g, "$1")
    .trim();
}

/**
 * Splits a single oversized thought at the strongest nearby punctuation.
 * Word boundaries are the final safety valve for captions with no punctuation.
 */
function splitOversizedThought(text, maxChars) {
  const parts = [];
  let rest = normalizeCaptionText(text);

  while (rest.length > maxChars) {
    const windowText = rest.slice(0, maxChars + 1);
    const lowerBound = Math.floor(maxChars * 0.55);
    let cut = -1;

    for (const pattern of [/[;:；：]\s*/g, /[,，]\s*/g, /\s/g]) {
      pattern.lastIndex = 0;
      let match;
      while ((match = pattern.exec(windowText))) {
        if (match.index >= lowerBound) cut = match.index + match[0].length;
      }
      if (cut > 0) break;
    }

    if (cut <= 0) cut = maxChars;
    parts.push(rest.slice(0, cut).trim());
    rest = rest.slice(cut).trim();
  }

  if (rest) parts.push(rest);
  return parts;
}

/**
 * Reconstructs complete sentences across raw caption boundaries. Each segment
 * keeps the timestamp of the first caption that contributed text. Character
 * and time limits prevent a malformed Supadata entry from becoming one giant
 * row while punctuation remains the preferred boundary.
 */
function groupTranscriptEntries(entries, limits = TRANSCRIPT_SEGMENT_LIMITS) {
  if (!Array.isArray(entries) || entries.length === 0) return [];

  const pieces = [];
  entries.forEach((entry, entryIndex) => {
    const text = normalizeCaptionText(entry?.text);
    if (!text) return;
    const start = Number.isFinite(Number(entry.start)) ? Number(entry.start) : 0;
    const duration = Math.max(0, Number(entry.duration) || 0);
    const sentenceParts =
      text.match(/[^.!?;:,。！？；：，]+(?:[.!?;:,。！？；：，]+["')\]”’）】」』]*|$)/g) ||
      [text];
    let consumedChars = 0;

    sentenceParts.forEach((sentencePart) => {
      const cleanPart = normalizeCaptionText(sentencePart);
      if (!cleanPart) return;
      const oversizedParts = splitOversizedThought(cleanPart, limits.maxChars);
      oversizedParts.forEach((part, partIndex) => {
        const ratio = text.length ? Math.min(1, consumedChars / text.length) : 0;
        pieces.push({
          text: part,
          start: start + duration * ratio,
          semanticEnd:
            /[.!?。！？]["')\]”’）】」』]*$/.test(part) ||
            oversizedParts.length > 1,
          clauseEnd: /[;:,；：，]["')\]”’）】」』]*$/.test(part),
          sourceOrder: `${entryIndex}:${partIndex}`,
        });
        consumedChars += part.length + 1;
      });
    });
  });

  const grouped = [];
  let current = null;

  const flush = () => {
    if (!current || !current.text.trim()) return;
    const index = grouped.length;
    const text = normalizeCaptionText(current.text);
    grouped.push({
      id: `segment-${index}-${Math.round(current.start * 1000)}`,
      start: current.start,
      text,
      texts: [text],
    });
    current = null;
  };

  pieces.forEach((piece) => {
    if (!current) current = { start: piece.start, text: "" };
    current.text = normalizeCaptionText(`${current.text} ${piece.text}`);
    const elapsed = Math.max(0, piece.start - current.start);
    const comfortablySized = current.text.length >= limits.minChars;
    const reachedIdeal = current.text.length >= limits.idealChars;
    const atNaturalBoundary =
      piece.semanticEnd ||
      (piece.clauseEnd &&
        (reachedIdeal ||
          current.text.length >= limits.maxChars ||
          elapsed >= limits.maxSeconds));
    const reachedGuardrail =
      atNaturalBoundary &&
      (current.text.length >= limits.maxChars || elapsed >= limits.maxSeconds);
    const reachedHardGuardrail =
      current.text.length >= Math.round(limits.maxChars * 1.2) ||
      elapsed >= limits.maxSeconds + 5;

    if (
      (atNaturalBoundary && (comfortablySized || elapsed >= 8)) ||
      (atNaturalBoundary && reachedIdeal) ||
      reachedGuardrail ||
      reachedHardGuardrail
    ) {
      flush();
    }
  });
  flush();

  return grouped;
}

// ============================================================
// INITIALIZATION
// ============================================================

async function loadPanelBehaviorSetting() {
  try {
    const stored = await chrome.storage.local.get(YTD_SETTINGS.STORAGE_KEY);
    const settings = YTD_SETTINGS.normalize(stored[YTD_SETTINGS.STORAGE_KEY]);
    keepPanelOpenAcrossTabs = settings.keepPanelOpenAcrossTabs !== false;
  } catch (_error) {
    keepPanelOpenAcrossTabs = true;
  }
}

chrome.storage?.onChanged?.addListener((changes, areaName) => {
  if (areaName === "local" && changes[YTD_SETTINGS.STORAGE_KEY]) {
    void loadPanelBehaviorSetting();
  }
});

document.addEventListener("DOMContentLoaded", async () => {
  setTranscriptModeButtons("original");
  setupEventListeners();
  await loadPanelBehaviorSetting();
  await evictOldCacheEntries(20);
  await refreshNativeHostButton();

  const configStatus = await chrome.runtime.sendMessage({
    action: "checkConfig",
  });

  if (!configStatus.hasSupadataKey || !configStatus.hasAiKey) {
    showConfigError(configStatus);
    return;
  }

  await checkCurrentTab();
});

// Listen for messages from the Digest button on YouTube page
chrome.runtime.onMessage.addListener((message, sender, sendResponse) => {
  if (message.action === "startDigestFromButton") {
    // Load the digest for the current video. Served from cache when we've
    // seen this video before (no API calls); fetched fresh otherwise.
    // (This used to force-clear the cache on every click, which silently
    // burned a transcript credit + analysis tokens per click.)
    checkCurrentTab();
    sendResponse({ success: true });
  }
  if (message.action === "transcriptProgress") {
    // Background is telling us the transcript fetch status changed
    updateLoading(message.title, message.subtitle);
    sendResponse({ success: true });
  }
  if (message.action === "noteSaved") {
    // Refresh notes list when a new note is saved
    const filterAll = document
      .getElementById("notesFilterAll")
      ?.classList.contains("active");
    loadNotes(filterAll ? null : currentVideoId);
    sendResponse({ success: true });
  }
  return false;
});

// ============================================================
// FOLLOW THE ACTIVE TAB
// ============================================================
// The panel watches which tab is in front of it and reacts:
//   - Front tab is NOT YouTube  -> the panel closes itself (window.close()).
//     We do this OURSELVES rather than relying only on the background
//     script's per-tab enable/disable, because Chrome doesn't reliably
//     apply per-tab panel state to tabs spawned in unusual ways (e.g. a
//     link opened from another app) — which let the panel linger on
//     non-YouTube pages.
//   - Front tab IS YouTube but on a different video -> refresh the digest.
//     YouTube is a single-page app (clicking a video swaps content without
//     a reload), so we track URL changes; startDigest() caches per video,
//     making re-checks instant and free for already-digested videos.
//
// Everything is scoped to the window this panel lives in: tab switches in
// OTHER browser windows must not close this panel or hijack its content.

let navigationRefreshTimer = null;
let panelWindowId = null;
chrome.windows.getCurrent().then((w) => {
  panelWindowId = w.id;
});

function scheduleDigestRefresh() {
  // Small delay lets YouTube finish rendering the new video's title and
  // description before we read them. Also collapses rapid-fire URL events
  // into a single refresh.
  clearTimeout(navigationRefreshTimer);
  navigationRefreshTimer = setTimeout(() => {
    checkCurrentTab();
  }, 600);
}

function panelIsShowingResults() {
  const results = document.getElementById("resultsState");
  return results && results.style.display !== "none";
}

/**
 * Reacts to the URL now in front of the panel: close on non-YouTube,
 * refresh the digest when the video changed.
 */
function handleFrontTabUrl(url) {
  if (!(url || "").startsWith("https://www.youtube.com")) {
    void saveCurrentTranscriptViewState();
    // Closing the panel here is what made it vanish when the user came back
    // to a YouTube tab: only a fresh click on the icon can reopen it. When
    // the panel is meant to stay open, show the welcome screen instead.
    if (keepPanelOpenAcrossTabs) {
      showState("welcome");
      return;
    }
    // Chrome does not reliably honor window.close() after an asynchronous
    // wait, so close in this same event callback.
    window.close();
    return;
  }

  const newVideoId = extractVideoId(url);
  // Refresh when the video changed, or when we're not currently showing
  // results (e.g. user went home, then clicked back into the same video).
  if (newVideoId !== currentVideoId || !panelIsShowingResults()) {
    scheduleDigestRefresh();
  }
}

/**
 * Gets the best URL from a tab update that can change the visible page.
 * The status events repeat the close request after Chrome commits the first
 * non-YouTube navigation, when an early URL event alone can be lost.
 */
function getNavigationUrl(changeInfo, tab) {
  if (changeInfo.url) return changeInfo.url;
  if (changeInfo.status !== "loading" && changeInfo.status !== "complete") {
    return "";
  }
  return tab.pendingUrl || tab.url || "";
}

// Fires when a tab starts or completes navigation, including YouTube's
// no-reload navigation. The completion event is a deliberate second close
// attempt for the first non-YouTube page.
chrome.tabs.onUpdated.addListener((tabId, changeInfo, tab) => {
  if (!tab.active) return;
  if (panelWindowId !== null && tab.windowId !== panelWindowId) return;
  const url = getNavigationUrl(changeInfo, tab);
  if (!url) return;
  handleFrontTabUrl(url);
});

// Fires when a different tab comes to the front — switching tabs, or a new
// tab being opened (including ones opened by clicking links in other apps).
chrome.tabs.onActivated.addListener(async ({ tabId, windowId }) => {
  if (panelWindowId !== null && windowId !== panelWindowId) return;
  try {
    const tab = await chrome.tabs.get(tabId);
    // Brand-new tabs may not have committed their URL yet — fall back to
    // the pending one so we judge where the tab is actually going.
    handleFrontTabUrl(tab.url || tab.pendingUrl || "");
  } catch (e) {
    // Tab closed before we could read it — nothing to do.
  }
});

function setupEventListeners() {
  // Tab switching
  document.querySelectorAll(".tab").forEach((tab) => {
    tab.addEventListener("click", () => switchTab(tab.dataset.tab));
  });

  // Error retry
  document.getElementById("errorBtn").addEventListener("click", () => {
    if (errorAction) {
      errorAction();
      return;
    }
    if (currentVideoId) {
      startDigest(currentVideoId, currentVideoUrl);
    }
  });

  document.getElementById("settingsBtn")?.addEventListener("click", () => {
    chrome.runtime.sendMessage({ action: "openOptions" });
  });

  document
    .getElementById("downloadVideoBtn")
    ?.addEventListener("click", downloadVideoLocally);

  // Transcript actions
  document
    .getElementById("copyTranscriptBtn")
    ?.addEventListener("click", copyTranscript);
  document
    .getElementById("exportTranscriptBtn")
    ?.addEventListener("click", exportTranscript);
  document
    .getElementById("exportSrtBtn")
    ?.addEventListener("click", exportTranscriptSrt);
  document
    .getElementById("exportClipsBtn")
    ?.addEventListener("click", exportClipsCsv);
  document
    .getElementById("exportObsidianBtn")
    ?.addEventListener("click", exportObsidianMd);
  document.querySelectorAll(".transcript-mode-btn").forEach((button) => {
    button.addEventListener("click", () => {
      handleDisplayLanguageModeChange(button.dataset.transcriptMode);
    });
  });
  setupTranscriptSearch();

  // pagehide also covers closing the side panel without a tab change.
  window.addEventListener("pagehide", () => {
    void saveCurrentTranscriptViewState();
  });

  // Follow playback button — re-enables auto-scroll after user scrolled away
  document
    .getElementById("followPlaybackBtn")
    ?.addEventListener("click", () => {
      autoScrollEnabled = true;
      document.getElementById("followPlaybackBtn").style.display = "none";
      // Jump straight back to the line currently being spoken. We scroll
      // directly (not via playbackTrackingTick) because the tick skips
      // entries that are already highlighted — and the current line almost
      // always IS highlighted, which made this button appear to do nothing.
      if (!scrollToActiveEntry()) {
        playbackTrackingTick(); // No highlight yet — let a tick establish one
      }
    });

  // Notes filter buttons
  document.getElementById("notesFilterThis")?.addEventListener("click", () => {
    setNotesFilter(false);
    loadNotes(currentVideoId);
  });
  document.getElementById("notesFilterAll")?.addEventListener("click", () => {
    setNotesFilter(true);
    loadNotes(null); // Load all notes
  });
}

function setNotesFilter(showAll) {
  const thisVideoButton = document.getElementById("notesFilterThis");
  const allNotesButton = document.getElementById("notesFilterAll");
  thisVideoButton?.classList.toggle("active", !showAll);
  thisVideoButton?.setAttribute("aria-pressed", String(!showAll));
  allNotesButton?.classList.toggle("active", showAll);
  allNotesButton?.setAttribute("aria-pressed", String(showAll));
}

// ============================================================
// VIDEO DETECTION
// ============================================================

async function checkCurrentTab() {
  try {
    // The panel belongs only to the active tab. Looking for another open
    // YouTube tab here can keep an old transcript visible on a non-YouTube
    // page, so never fall back to background tabs.
    const tabs = await chrome.tabs.query({
      active: true,
      lastFocusedWindow: true,
    });
    const tab = tabs[0] || null;

    debugLog("[YouTube Digest Panel] Found tab:", tab?.id, tab?.url);

    if (!tab?.url) {
      showState("welcome");
      return;
    }

    if (!tab.url.startsWith("https://www.youtube.com")) {
      handleFrontTabUrl(tab.url);
      return;
    }

    // Store the tab ID for reliable messaging later
    youtubeTabId = tab.id;

    const videoId = extractVideoId(tab.url);

    if (videoId) {
      currentVideoUrl = tab.url;

      try {
        // Route through background script for reliable message passing
        const result = await chrome.runtime.sendMessage({
          action: "relayToContent",
          payload: { action: "getVideoInfo" },
        });
        debugLog("[YouTube Digest Panel] getVideoInfo result:", result);
        if (result.success && result.response) {
          currentVideoTitle = result.response.title || "";
          currentChannelName = result.response.channelName || "";
          currentVideoDescription = result.response.description || "";
          currentVideoDuration = result.response.duration || 0;
        }
      } catch (e) {
        console.error("[YouTube Digest Panel] getVideoInfo error:", e);
        currentVideoTitle = "";
        currentChannelName = "";
        currentVideoDescription = "";
        currentVideoDuration = 0;
      }

      startDigest(videoId, tab.url);
    } else {
      showState("welcome");
    }
  } catch (error) {
    console.error("Tab check error:", error);
    showState("welcome");
  }
}

function extractVideoId(url) {
  try {
    const urlObj = new URL(url);

    if (
      urlObj.hostname.includes("youtube.com") &&
      urlObj.searchParams.has("v")
    ) {
      return urlObj.searchParams.get("v");
    }

    if (urlObj.hostname === "youtu.be") {
      return urlObj.pathname.slice(1);
    }

    if (urlObj.pathname.startsWith("/embed/")) {
      return urlObj.pathname.split("/")[2];
    }

    return null;
  } catch {
    return null;
  }
}

// ============================================================
// DIGEST PIPELINE
// ============================================================

async function startDigest(videoId, videoUrl) {
  // Check if we already have this video loaded in memory
  if (videoId === currentVideoId && currentAnalysis) {
    showState("results");
    return;
  }

  const videoChanged = videoId !== currentVideoId;

  // Every video change invalidates observer work and in-flight translations.
  if (videoChanged) {
    translationGeneration += 1;
    if (transcriptScrollObserver) transcriptScrollObserver.disconnect();
    transcriptScrollObserver = null;
    resetTranscriptSearch();
    lastTranscriptScrollTop = 0;
    pendingTranscriptViewState = await loadTranscriptViewState(videoId);
    // An unseen video always starts in Original, so opening it never spends
    // translation tokens. A saved choice is restored only for this video.
    currentTranscriptMode = await loadDisplayLanguageMode(videoId);
    document
      .getElementById("contentArea")
      ?.classList.toggle(
        "restoring-transcript-view",
        Boolean(pendingTranscriptViewState),
      );
  }

  // Check cache for this video
  const cached = await loadFromCache(videoId);
  if (cached) {
    debugLog("Loading from cache:", videoId);
    currentVideoId = videoId;
    currentVideoUrl = videoUrl;
    currentAnalysis = cached.analysis || null;
    currentTranscript = cached.transcript;
    currentTranscriptText = cached.transcriptText;
    currentTranscriptTimestamped = cached.transcriptTimestamped;
    currentTranscriptLanguage = cached.transcriptLanguage || null;
    isAnalysisLoading = false;

    // Restore semantic-segment translations from persistent storage.
    if (cached.paragraphCache) {
      for (const [key, value] of Object.entries(cached.paragraphCache)) {
        transcriptParagraphCache.set(key, value);
      }
    }
    if (cached.interfaceCache) {
      for (const [key, value] of Object.entries(cached.interfaceCache)) {
        interfaceTranslationCache.set(key, value);
      }
    }

    if (currentVideoTitle || currentChannelName) {
      const videoInfo = document.getElementById("videoInfo");
      document.getElementById("videoTitle").textContent = currentVideoTitle;
      document.getElementById("videoChannel").textContent = currentChannelName;
      videoInfo.style.display = "block";
    }

    // Always render transcript first
    renderTranscript();

    // Render analysis if we have it cached
    if (currentAnalysis) {
      renderAnalysisResults(currentAnalysis);
      highlightMomentsOnPage(currentAnalysis.keyMoments);
    }

    showState("results");
    document.getElementById("tabsNav").style.display = "flex";
    restorePendingTranscriptViewState(videoId);

    // Load notes for this video
    loadNotes(videoId);

    // Setup explain feature
    setupExplainFeature();
    if (currentTranscriptMode !== "original") translateTranscript();
    return;
  }

  currentVideoId = videoId;
  currentVideoUrl = videoUrl;
  currentAnalysis = null;
  currentTranscript = null;
  currentTranscriptText = null;
  currentTranscriptTimestamped = null;
  currentTranscriptLanguage = null;
  isAnalysisLoading = false;

  if (currentVideoTitle || currentChannelName) {
    const videoInfo = document.getElementById("videoInfo");
    document.getElementById("videoTitle").textContent = currentVideoTitle;
    document.getElementById("videoChannel").textContent = currentChannelName;
    videoInfo.style.display = "block";
  }

  showState("loading");
  updateLoading("Fetching transcript", "");

  const transcriptResult = await chrome.runtime.sendMessage({
    action: "fetchTranscript",
    videoId: videoId,
  });

  if (!transcriptResult.success) {
    if (transcriptResult.error === "NO_SUPADATA_KEY") {
      showError(
        "API key missing",
        "Add your Supadata API key in YouTube Digest Settings.",
      );
      return;
    }
    showError(
      "No transcript found",
      transcriptResult.message || transcriptResult.error,
    );
    return;
  }

  currentTranscript = transcriptResult.transcript;
  currentTranscriptText = transcriptResult.transcriptText;
  currentTranscriptTimestamped = transcriptResult.transcriptTextTimestamped;
  currentTranscriptLanguage = transcriptResult.language || null;

  // Render transcript immediately (no LLM needed)
  renderTranscript();
  showState("results");
  document.getElementById("tabsNav").style.display = "flex";
  restorePendingTranscriptViewState(videoId);

  // Load notes for this video
  loadNotes(videoId);

  // Setup explain feature for text selection
  setupExplainFeature();
  if (currentTranscriptMode !== "original") translateTranscript();

  // Save transcript to cache (without analysis)
  await saveToCache(videoId);

  // DON'T run LLM analysis automatically - wait for user to click Overview tab
  // This saves tokens when user just wants to see the transcript
}

// ============================================================
// RENDERING
// ============================================================

function interfaceTranslationCacheKey(surface, id, text) {
  return `${currentVideoId || "none"}:zh:${surface}:${id}:${text}`;
}

function getInterfaceTranslation(surface, id, text) {
  return interfaceTranslationCache.get(
    interfaceTranslationCacheKey(surface, id, text),
  );
}

function renderLocalizedContent(text, surface, id) {
  const original = String(text || "");
  if (!original) return "";
  const cacheKey = interfaceTranslationCacheKey(surface, id, original);
  const translated = getInterfaceTranslation(surface, id, original);
  if (currentTranscriptMode === "original") return escapeHtml(original);

  const translation = translated
    ? escapeHtml(translated)
    : interfaceTranslationFailures.has(cacheKey)
      ? '<span class="translation-error">Translation unavailable.</span>'
      : '<span class="translation-pending">Translating...</span>';
  if (currentTranscriptMode === "bilingual") {
    return `<span class="localized-copy"><span class="localized-original">${escapeHtml(original)}</span><span class="localized-translation">${translation}</span></span>`;
  }
  return `<span class="localized-copy"><span class="localized-translation">${translation}</span></span>`;
}

function getLocalizedPlainText(text, surface, id) {
  const original = String(text || "");
  const translated = getInterfaceTranslation(surface, id, original);
  if (currentTranscriptMode === "zh") return translated || original;
  if (currentTranscriptMode === "bilingual" && translated) {
    return `${original}\n\n${translated}`;
  }
  return original;
}

async function translateInterfaceSegments(surface, segments, rerender) {
  if (currentTranscriptMode === "original" || !segments.length) return;
  const generation = translationGeneration;
  const videoId = currentVideoId;
  const missing = segments
    .filter((segment) => segment.text)
    .map((segment) => ({
      ...segment,
      cacheKey: interfaceTranslationCacheKey(
        surface,
        segment.id,
        segment.text,
      ),
    }))
    .filter(
      (segment) =>
        !interfaceTranslationCache.has(segment.cacheKey) &&
        !interfaceTranslationFailures.has(segment.cacheKey) &&
        !interfaceTranslationInFlight.has(segment.cacheKey),
    );
  if (!missing.length) return;

  missing.forEach((segment) => interfaceTranslationInFlight.add(segment.cacheKey));
  setTranslatingSpinner(true);
  try {
    for (
      let start = 0;
      start < missing.length;
      start += TRANSLATION_BATCH_SIZE
    ) {
      const batch = missing.slice(start, start + TRANSLATION_BATCH_SIZE);
      let result;
      try {
        result = await sendTranslationMessage({
          action: "translateContent",
          content: {
            segments: batch.map(({ id, text }) => ({ id, text })),
          },
          contentType: "interfaceBatch",
          targetLanguage: "zh",
          videoTitle: currentVideoTitle,
        });
      } catch (error) {
        console.error("[YouTube Digest] Interface batch error:", error);
        result = { success: false, error: error.message };
      }
      if (
        generation !== translationGeneration ||
        videoId !== currentVideoId ||
        currentTranscriptMode === "original"
      ) {
        return;
      }
      const aligned = alignTranslatedSegmentBatch(
        batch,
        result?.success ? result.translatedContent?.segments : [],
      );
      aligned.forEach((item, index) => {
        if (item.text) {
          interfaceTranslationCache.set(batch[index].cacheKey, item.text);
        } else {
          interfaceTranslationFailures.add(batch[index].cacheKey);
        }
      });
      // Match the Transcript UX: reveal and persist every small batch as soon
      // as it returns instead of waiting for the full Overview or Notes list.
      rerender();
      await updateCache();
    }
  } catch (error) {
    console.error("[YouTube Digest] Interface translation error:", error);
    missing.forEach((segment) =>
      interfaceTranslationFailures.add(segment.cacheKey),
    );
  } finally {
    missing.forEach((segment) => interfaceTranslationInFlight.delete(segment.cacheKey));
    setTranslatingSpinner(false);
  }
}

function getOverviewTranslationSegments() {
  if (!currentAnalysis) return [];
  const segments = [];
  (currentAnalysis.chapters || []).forEach((chapter, index) => {
    if (chapter.title) {
      segments.push({ id: `chapter-${index}-title`, text: chapter.title });
    }
    if (chapter.summary) {
      segments.push({ id: `chapter-${index}-summary`, text: chapter.summary });
    }
  });
  [...(currentAnalysis.keyQuotes || [])]
    .sort((a, b) => (a.timestampSeconds || 0) - (b.timestampSeconds || 0))
    .forEach((quote, index) => {
      if (quote.quote) segments.push({ id: `quote-${index}`, text: quote.quote });
    });
  return segments;
}

function translateOverviewContent() {
  return translateInterfaceSegments(
    "overview",
    getOverviewTranslationSegments(),
    () => {
      const contentArea = document.getElementById("contentArea");
      const scrollTop = contentArea?.scrollTop || 0;
      renderAnalysisResults(currentAnalysis);
      if (contentArea) contentArea.scrollTop = scrollTop;
    },
  );
}

function getNoteTranslationId(note, index) {
  const stablePart = String(note.id || note.createdAt || index)
    .replace(/[^A-Za-z0-9_-]/g, "-")
    .slice(0, 96);
  return `note-${stablePart || index}`;
}

function translateNotesContent() {
  const segments = currentNotes.map((note, index) => ({
    id: getNoteTranslationId(note, index),
    text: note.text || "",
  }));
  return translateInterfaceSegments("notes", segments, () => {
    const contentArea = document.getElementById("contentArea");
    const scrollTop = contentArea?.scrollTop || 0;
    renderNotes(currentNotes, currentNotesFilterVideoId);
    if (contentArea) contentArea.scrollTop = scrollTop;
  });
}

/**
 * Renders the analysis results into the Overview tab.
 * Shows chapters and key quotes only.
 */
function renderAnalysisResults(analysis) {
  // Chapters
  const chapterList = document.getElementById("chapterList");
  chapterList.innerHTML = "";
  (analysis.chapters || []).forEach((chapter, index) => {
    const li = document.createElement("li");
    li.className = "chapter-item";
    li.dataset.seconds = chapter.timestampSeconds;
    li.innerHTML = `
      <span class="chapter-timestamp">${escapeHtml(chapter.timestamp)}</span>
      <div class="chapter-content">
        <span class="chapter-title">${renderLocalizedContent(chapter.title, "overview", `chapter-${index}-title`)}</span>
        <span class="chapter-summary">${renderLocalizedContent(chapter.summary || "", "overview", `chapter-${index}-summary`)}</span>
      </div>
    `;
    li.addEventListener("click", () => {
      debugLog(
        "[YouTube Digest Panel] Chapter clicked:",
        chapter.timestamp,
        chapter.timestampSeconds,
      );
      seekTo(chapter.timestampSeconds);
    });
    chapterList.appendChild(li);
  });

  // Quotes - sort by timestamp (chronological order)
  const quotesList = document.getElementById("quotesList");
  quotesList.innerHTML = "";
  const sortedQuotes = [...(analysis.keyQuotes || [])].sort(
    (a, b) => (a.timestampSeconds || 0) - (b.timestampSeconds || 0),
  );
  sortedQuotes.forEach((quote, index) => {
    const div = document.createElement("div");
    div.className = "quote-item";
    div.dataset.seconds = quote.timestampSeconds;
    div.innerHTML = `
      <div class="quote-text">${renderLocalizedContent(quote.quote, "overview", `quote-${index}`)}</div>
      <div class="quote-meta">
        <span class="quote-timestamp">${escapeHtml(quote.timestamp)}</span>
        <div class="quote-actions">
          <button class="quote-save-note-btn" title="Save this quote as a note">Note</button>
          <button class="quote-copy-btn" title="Copy this quote">Copy</button>
          <button class="quote-card-btn" title="Render this quote as a card image (PNG)">Card</button>
        </div>
      </div>
    `;
    div.addEventListener("click", () => {
      debugLog(
        "[YouTube Digest Panel] Quote clicked:",
        quote.timestamp,
        quote.timestampSeconds,
      );
      seekTo(quote.timestampSeconds);
    });

    const quoteCopyBtn = div.querySelector(".quote-copy-btn");
    quoteCopyBtn.addEventListener("click", async (e) => {
      e.stopPropagation();
      try {
        await navigator.clipboard.writeText(
          getLocalizedPlainText(quote.quote, "overview", `quote-${index}`),
        );
        quoteCopyBtn.textContent = "Copied";
        setTimeout(() => {
          quoteCopyBtn.textContent = "Copy";
        }, 1500);
      } catch (err) {
        console.error("Copy failed:", err);
      }
    });

    const quoteSaveNoteBtn = div.querySelector(".quote-save-note-btn");
    quoteSaveNoteBtn.addEventListener("click", async (e) => {
      e.stopPropagation();
      await saveQuoteAsNote(quote, quoteSaveNoteBtn);
    });

    const quoteCardBtn = div.querySelector(".quote-card-btn");
    quoteCardBtn.addEventListener("click", (e) => {
      e.stopPropagation();
      openQuoteCardModal(quote, index);
    });

    quotesList.appendChild(div);
  });

  if (
    currentTranscriptMode !== "original" &&
    resultTabIsActive("overview")
  ) {
    void translateOverviewContent();
  }

  renderTimelineHeatmap();
}

/**
 * Saves a key quote as a timestamped note.
 */
async function saveQuoteAsNote(quote, btn) {
  if (!currentVideoId) return;

  const originalText = btn.textContent;
  btn.textContent = "Saving...";
  btn.disabled = true;

  try {
    const result = await chrome.runtime.sendMessage({
      action: "saveNote",
      videoId: currentVideoId,
      timestamp: quote.timestampSeconds,
      videoTitle: currentVideoTitle,
      channelName: currentChannelName,
    });

    if (result.success) {
      btn.textContent = "Saved";
      setTimeout(() => {
        btn.textContent = originalText;
        btn.disabled = false;
      }, 1500);
      // Refresh notes list if on Notes tab
      loadNotes(currentVideoId);
    } else {
      console.error("[YouTube Digest] Save quote as note failed:", result.error);
      btn.textContent = "Error";
      setTimeout(() => {
        btn.textContent = originalText;
        btn.disabled = false;
      }, 1500);
    }
  } catch (error) {
    console.error("[YouTube Digest] Save quote as note error:", error);
    btn.textContent = "Error";
    setTimeout(() => {
      btn.textContent = originalText;
      btn.disabled = false;
    }, 1500);
  }
}

/**
 * Legacy function for backwards compatibility with cached data.
 * Renders both transcript and analysis.
 */
function renderResults(analysis) {
  renderAnalysisResults(analysis);

  renderTranscript();

  document.getElementById("tabsNav").style.display = "flex";

  // Setup explain feature for text selection
  setupExplainFeature();
}

/**
 * Returns true while the user has a range of text selected.
 * Transcript row clicks must not seek in that state: the click emitted after
 * selection mouseup belongs to the selection/explain interaction, not playback.
 */
function hasNonCollapsedTextSelection() {
  const selection = window.getSelection();
  return Boolean(
    selection && selection.rangeCount > 0 && !selection.isCollapsed,
  );
}

/**
 * Preserves normal row-click seeking while keeping text selection inert.
 */
function seekFromTranscriptEntryClick(event, seconds) {
  if (hasNonCollapsedTextSelection()) {
    event.preventDefault();
    event.stopPropagation();
    return;
  }

  seekTo(seconds);
}

function renderTranscript() {
  if (!currentTranscript) return;

  const transcriptList = document.getElementById("transcriptList");
  transcriptList.innerHTML = "";

  const existingBadge = document.getElementById("transcriptSourceBadge");
  if (existingBadge) existingBadge.remove();

  // Group entries using smart sentence-boundary + time-guardrail logic
  const grouped = groupTranscriptEntries(currentTranscript);

  grouped.forEach((group) => {
    const div = document.createElement("div");
    div.className = "transcript-entry";
    div.dataset.seconds = group.start;

    const minutes = Math.floor(group.start / 60);
    const seconds = Math.floor(group.start % 60);
    const timestamp = `${minutes}:${String(seconds).padStart(2, "0")}`;

    div.innerHTML = `
      <span class="transcript-time">${timestamp}</span>
      <span class="transcript-text">${renderSubtitleInlineMarkup(group.text)}</span>
    `;

    div.addEventListener("click", (event) =>
      seekFromTranscriptEntryClick(event, group.start),
    );
    transcriptList.appendChild(div);
  });

  // Reapply an active query after a language mode rerenders the transcript.
  refreshTranscriptSearch({ preserveIndex: false, scroll: false });

  renderTimelineHeatmap();

  // Start tracking video playback for auto-scroll
  startPlaybackTracking();
}

// ============================================================
// TRANSCRIPT SEARCH
// ============================================================

/**
 * Finds separate, case-insensitive literal matches. A literal search is
 * important here because punctuation such as "." must be treated as transcript
 * text, not as a regular expression command.
 */
function findLiteralTranscriptMatches(text, query) {
  const source = String(text || "");
  const needle = String(query || "").trim();
  if (!needle) return [];

  const escapedNeedle = needle.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const matcher = new RegExp(escapedNeedle, "giu");
  const matches = [];
  for (const match of source.matchAll(matcher)) {
    matches.push({ start: match.index, end: match.index + match[0].length });
  }

  return matches;
}

/**
 * Removes old marks before a new search. Restoring plain text first prevents
 * nested marks when the user types one more letter into the search field.
 */
function clearTranscriptSearchHighlights() {
  document
    .querySelectorAll("#transcriptList mark.transcript-search-highlight")
    .forEach((mark) => {
      const parent = mark.parentNode;
      mark.replaceWith(document.createTextNode(mark.textContent || ""));
      parent?.normalize();
    });

  document
    .querySelectorAll("#transcriptList .transcript-entry.search-current")
    .forEach((row) => row.classList.remove("search-current"));
}

/**
 * Replaces matching parts of one text node with mark elements. We collect all
 * text nodes before changing the DOM, so each replacement is safe and stable.
 */
function markTranscriptTextNode(textNode, query) {
  const ranges = findLiteralTranscriptMatches(textNode.nodeValue, query);
  if (!ranges.length) return [];

  const fragment = document.createDocumentFragment();
  const marks = [];
  let cursor = 0;

  ranges.forEach(({ start, end }) => {
    if (start > cursor) {
      fragment.appendChild(
        document.createTextNode(textNode.nodeValue.slice(cursor, start)),
      );
    }

    const mark = document.createElement("mark");
    mark.className = "transcript-search-highlight";
    mark.textContent = textNode.nodeValue.slice(start, end);
    fragment.appendChild(mark);
    marks.push(mark);
    cursor = end;
  });

  if (cursor < textNode.nodeValue.length) {
    fragment.appendChild(
      document.createTextNode(textNode.nodeValue.slice(cursor)),
    );
  }

  textNode.parentNode.replaceChild(fragment, textNode);
  return marks;
}

/**
 * Updates the result count and navigation buttons from the current search
 * state. The live output gives the same information to screen reader users.
 */
function updateTranscriptSearchControls(query) {
  const count = document.getElementById("transcriptSearchCount");
  const previous = document.getElementById("transcriptSearchPrevBtn");
  const next = document.getElementById("transcriptSearchNextBtn");
  const hasMatches = transcriptSearchMatches.length > 0;

  if (count) {
    count.textContent = !query
      ? ""
      : hasMatches
        ? `${transcriptSearchIndex + 1} of ${transcriptSearchMatches.length}`
        : "No matches";
  }
  if (previous) previous.disabled = !hasMatches;
  if (next) next.disabled = !hasMatches;
}

/**
 * Shows which match is current. Search navigation pauses automatic transcript
 * following, so playback cannot pull the user away from the result they found.
 */
function revealCurrentTranscriptSearchMatch({ scroll = true } = {}) {
  transcriptSearchMatches.forEach((mark) => mark.classList.remove("current"));
  document
    .querySelectorAll("#transcriptList .transcript-entry.search-current")
    .forEach((row) => row.classList.remove("search-current"));

  const mark = transcriptSearchMatches[transcriptSearchIndex];
  if (!mark) return;

  mark.classList.add("current");
  mark.closest(".transcript-entry")?.classList.add("search-current");

  if (!scroll) return;
  if (autoScrollInterval) {
    autoScrollEnabled = false;
    document.getElementById("followPlaybackBtn").style.display = "block";
  }
  mark.scrollIntoView({ behavior: "smooth", block: "center" });
}

/**
 * Searches the transcript that is visible now. This means Original searches
 * source subtitles, Chinese searches translated text, and Bilingual searches
 * both columns. Translated rows call this again as their text arrives.
 */
function refreshTranscriptSearch({ preserveIndex = false, scroll = true } = {}) {
  const input = document.getElementById("transcriptSearchInput");
  const clearButton = document.getElementById("transcriptSearchClearBtn");
  const query = String(input?.value || "").trim();
  const previousIndex = transcriptSearchIndex;

  clearTranscriptSearchHighlights();
  transcriptSearchMatches = [];
  transcriptSearchIndex = -1;
  if (clearButton) clearButton.hidden = !input?.value;

  if (!query) {
    updateTranscriptSearchControls(query);
    return;
  }

  document
    .querySelectorAll("#transcriptList .transcript-entry")
    .forEach((row) => {
      const content = row.querySelector(".transcript-text, .transcript-copy");
      if (!content) return;

      const textNodes = [];
      const walker = document.createTreeWalker(
        content,
        NodeFilter.SHOW_TEXT,
        {
          acceptNode(node) {
            const parent = node.parentElement;
            if (!node.nodeValue || parent?.closest("button")) {
              return NodeFilter.FILTER_REJECT;
            }
            return NodeFilter.FILTER_ACCEPT;
          },
        },
      );
      while (walker.nextNode()) textNodes.push(walker.currentNode);
      textNodes.forEach((node) => {
        transcriptSearchMatches.push(...markTranscriptTextNode(node, query));
      });
    });

  if (transcriptSearchMatches.length) {
    transcriptSearchIndex = preserveIndex
      ? Math.min(Math.max(previousIndex, 0), transcriptSearchMatches.length - 1)
      : 0;
    revealCurrentTranscriptSearchMatch({ scroll });
  }
  updateTranscriptSearchControls(query);
}

/**
 * Moves through results in a loop, like the browser's built-in Find control.
 */
function moveTranscriptSearch(direction) {
  if (!transcriptSearchMatches.length) return;
  transcriptSearchIndex =
    (transcriptSearchIndex + direction + transcriptSearchMatches.length) %
    transcriptSearchMatches.length;
  revealCurrentTranscriptSearchMatch();
  updateTranscriptSearchControls(
    document.getElementById("transcriptSearchInput")?.value.trim(),
  );
}

/**
 * Clears search when the user opens a different video. A query for the old
 * video is unlikely to help and can make the next transcript look empty.
 */
function resetTranscriptSearch({ focus = false } = {}) {
  const input = document.getElementById("transcriptSearchInput");
  if (input) input.value = "";
  refreshTranscriptSearch({ scroll: false });
  if (focus) input?.focus();
}

/**
 * Wires mouse and keyboard controls once when the side panel starts.
 */
function setupTranscriptSearch() {
  const input = document.getElementById("transcriptSearchInput");
  const clearButton = document.getElementById("transcriptSearchClearBtn");
  const previous = document.getElementById("transcriptSearchPrevBtn");
  const next = document.getElementById("transcriptSearchNextBtn");
  if (!input) return;

  input.addEventListener("input", () => refreshTranscriptSearch());
  input.addEventListener("keydown", (event) => {
    if (event.key === "Enter") {
      event.preventDefault();
      moveTranscriptSearch(event.shiftKey ? -1 : 1);
    } else if (event.key === "Escape" && input.value) {
      event.preventDefault();
      resetTranscriptSearch({ focus: true });
    }
  });

  clearButton?.addEventListener("click", () => {
    resetTranscriptSearch({ focus: true });
  });
  previous?.addEventListener("click", () => moveTranscriptSearch(-1));
  next?.addEventListener("click", () => moveTranscriptSearch(1));
}

function getDisplayedTranscriptText() {
  if (currentTranscriptMode === "original") return currentTranscriptText || "";
  return getActiveTranscriptSegments()
    .map((segment) => {
      const translated = transcriptParagraphCache.get(
        transcriptTranslationCacheKey(segment),
      );
      if (currentTranscriptMode === "zh") return translated || segment.text;
      return translated ? `${segment.text}\n${translated}` : segment.text;
    })
    .join("\n\n");
}

function copyTranscript() {
  copyToClipboardWithFeedback(getDisplayedTranscriptText(), "copyTranscriptBtn");
}

function exportTranscript() {
  const transcriptContent = getDisplayedTranscriptText();
  const videoUrl = `https://youtube.com/watch?v=${currentVideoId}`;

  let exportText = "";
  exportText += `TRANSCRIPT\n`;
  exportText += `${"=".repeat(60)}\n\n`;
  exportText += `Title: ${currentVideoTitle || "Unknown"}\n`;
  exportText += `Channel: ${currentChannelName || "Unknown"}\n`;
  exportText += `URL: ${videoUrl}\n`;
  exportText += `\n${"—".repeat(60)}\n\n`;

  if (currentVideoDescription) {
    exportText += `DESCRIPTION:\n${currentVideoDescription}\n`;
    exportText += `\n${"—".repeat(60)}\n\n`;
  }

  exportText += `TRANSCRIPT:\n\n${transcriptContent}\n`;
  exportText += `\n${"—".repeat(60)}\n`;
  exportText += `Exported by YouTube Digest\n`;

  const filename = `${sanitizeFilename(currentVideoTitle)}-transcript.txt`;
  downloadTextFile(exportText, filename);
}

// ============================================================
// UI STATE MANAGEMENT
// ============================================================

function showState(state) {
  document.getElementById("welcomeState").style.display =
    state === "welcome" ? "flex" : "none";
  document.getElementById("loadingState").style.display =
    state === "loading" ? "block" : "none";
  document.getElementById("errorState").style.display =
    state === "error" ? "block" : "none";
  const uploadEl = document.getElementById("uploadState");
  if (uploadEl) uploadEl.style.display = "none"; // Upload state removed — always hidden
  document.getElementById("resultsState").style.display =
    state === "results" ? "block" : "none";

  // The tab bar only belongs on the results view. We toggle it HERE, in one
  // place, so it tracks the view automatically. Previously each caller had to
  // remember to re-show it after showState("results"), and one path forgot —
  // which is why the tabs could vanish when re-opening an already-analyzed video.
  document.getElementById("tabsNav").style.display =
    state === "results" ? "flex" : "none";
  document.getElementById("transcriptModeControl").style.display =
    state === "results" ? "inline-flex" : "none";

  if (state !== "results") {
    stopPlaybackTracking();
  }
}

function updateLoading(title, subtitle) {
  document.getElementById("loadingText").textContent = title;
  document.getElementById("loadingSubtext").textContent = subtitle;
}

function showError(title, message) {
  errorAction = null;
  showState("error");
  document.getElementById("errorTitle").textContent = title;
  document.getElementById("errorMessage").textContent = message;
  document.getElementById("errorBtn").textContent = "Try Again";
}

function showConfigError(configStatus) {
  const missingKeys = [];
  if (!configStatus.hasSupadataKey) missingKeys.push("Supadata");
  if (!configStatus.hasAiKey) missingKeys.push("AI provider");

  showState("error");
  document.getElementById("errorTitle").textContent = "API Keys Missing";
  document.getElementById("errorMessage").textContent =
    `Add your ${missingKeys.join(" and ")} API key${missingKeys.length === 1 ? "" : "s"} in YouTube Digest Settings.`;
  document.getElementById("errorBtn").textContent = "Open Settings";
  errorAction = () => chrome.runtime.sendMessage({ action: "openOptions" });
}

// ============================================================
// TAB SWITCHING
// ============================================================

function switchTab(tabName) {
  // Capture the transcript position before another tab reuses the same scroll
  // area. Scrolling Overview or Notes must not replace this value.
  if (tabName !== "transcript" && transcriptTabIsActive()) {
    captureCurrentTranscriptScrollTop();
    dismissSelectionActions(true);
  }

  document.querySelectorAll(".tab").forEach((tab) => {
    tab.classList.toggle("active", tab.dataset.tab === tabName);
  });

  document.querySelectorAll(".tab-panel").forEach((panel) => {
    panel.classList.toggle("active", panel.dataset.panel === tabName);
  });

  // Start/stop playback tracking based on which tab is active
  if (tabName === "transcript") {
    // Notes always opens at the top, so restore the independent transcript
    // reading position when the user returns here.
    requestAnimationFrame(() => {
      const contentArea = document.getElementById("contentArea");
      if (!contentArea || !transcriptTabIsActive()) return;
      lastAutoScrollTime = Date.now();
      contentArea.scrollTop = lastTranscriptScrollTop;
    });
    startPlaybackTracking();
  } else {
    stopPlaybackTracking();
  }

  // Saved notes are stored newest first. Open Notes at the top so the note the
  // user just created is the first item they see.
  if (tabName === "notes") {
    requestAnimationFrame(() => {
      const contentArea = document.getElementById("contentArea");
      const notesPanelIsActive = document.querySelector(
        '.tab-panel[data-panel="notes"].active',
      );
      if (contentArea && notesPanelIsActive) contentArea.scrollTop = 0;
    });
  }

  // Translate only the visible tab. This prevents hidden surfaces from using
  // tokens or competing with the batch queue the user is waiting for.
  if (tabName === "overview") {
    if (!currentAnalysis && !isAnalysisLoading) {
      triggerAnalysis();
    } else if (currentAnalysis && currentTranscriptMode !== "original") {
      void translateOverviewContent();
    }
  } else if (
    tabName === "notes" &&
    currentTranscriptMode !== "original"
  ) {
    void translateNotesContent();
  } else if (
    tabName === "transcript" &&
    currentTranscriptMode !== "original" &&
    !transcriptScrollObserver
  ) {
    void translateTranscript();
  }
}

/**
 * Triggers the LLM analysis (lazy-loaded when user clicks Overview or Quotes tab).
 * This saves tokens by not running analysis until needed.
 */
async function triggerAnalysis() {
  if (!currentTranscriptTimestamped || isAnalysisLoading || currentAnalysis)
    return;

  isAnalysisLoading = true;

  // Show loading indicators in the Overview tab
  const chapterList = document.getElementById("chapterList");
  const quotesList = document.getElementById("quotesList");

  if (chapterList)
    chapterList.innerHTML =
      '<li class="chapter-item" style="color: var(--text-muted); border: none;">Loading chapters...</li>';
  if (quotesList)
    quotesList.innerHTML =
      '<div class="quote-item" style="color: var(--text-muted); border-left-color: var(--border);">Loading quotes...</div>';

  try {
    const analysisResult = await chrome.runtime.sendMessage({
      action: "analyzeTranscript",
      transcriptText: currentTranscriptTimestamped,
      videoTitle: currentVideoTitle,
      channelName: currentChannelName,
      videoDescription: currentVideoDescription,
      videoDuration: currentVideoDuration,
    });

    if (!analysisResult.success) {
      if (chapterList)
        chapterList.innerHTML = `<li class="chapter-item" style="color: var(--accent); border: none;">Analysis failed: ${escapeHtml(analysisResult.error || "Unknown error")}</li>`;
      isAnalysisLoading = false;
      return;
    }

    currentAnalysis = analysisResult.analysis;
    renderAnalysisResults(currentAnalysis);
    highlightMomentsOnPage(currentAnalysis.keyMoments);

    // Save to cache now that we have analysis
    await saveToCache(currentVideoId);
  } catch (error) {
    console.error("[YouTube Digest Panel] Analysis error:", error);
    if (chapterList)
      chapterList.innerHTML = `<li class="chapter-item" style="color: var(--accent); border: none;">Error: ${escapeHtml(error.message)}</li>`;
  }

  isAnalysisLoading = false;
}

// ============================================================
// TIMESTAMP / SEEK
// ============================================================

async function seekTo(seconds) {
  debugLog("[YouTube Digest Panel] seekTo called with:", seconds);
  if (seconds === undefined || seconds === null) {
    debugLog("[YouTube Digest Panel] seekTo aborted - no seconds value");
    return;
  }

  const payload = {
    action: "seekTo",
    seconds: Number(seconds),
  };

  try {
    // Try direct messaging to the stored YouTube tab first (fastest/reliable)
    if (youtubeTabId) {
      try {
        await chrome.tabs.sendMessage(youtubeTabId, payload);
        debugLog("[YouTube Digest Panel] seekTo direct success");
        return;
      } catch (directErr) {
        debugLog(
          "[YouTube Digest Panel] Direct seekTo failed, falling back to relay:",
          directErr.message,
        );
      }
    }

    // Fallback: route through background script
    const result = await chrome.runtime.sendMessage({
      action: "relayToContent",
      payload,
    });
    debugLog("[YouTube Digest Panel] seekTo relay result:", result);
  } catch (error) {
    console.error("[YouTube Digest Panel] seekTo error:", error);
  }
}

/**
 * Plays a saved note at its timestamp.
 * - If the note belongs to the video currently open, we seek the player in place.
 * - If it belongs to a DIFFERENT video (e.g. viewing "All Notes"), seeking the
 *   current player would jump to the wrong content, so we open that video in a
 *   new tab at the right timestamp instead.
 */
function playNote(note) {
  if (note.videoId && note.videoId === currentVideoId) {
    seekTo(note.timestampSeconds);
  } else {
    // note.timestampedUrl already includes the &t=<seconds>s anchor
    chrome.tabs.create({ url: note.timestampedUrl });
  }
}

async function highlightMomentsOnPage(moments) {
  if (!moments || !moments.length) return;

  try {
    // Route through background script for reliable message passing
    await chrome.runtime.sendMessage({
      action: "relayToContent",
      payload: {
        action: "highlightMoments",
        moments: moments,
        videoDuration: currentVideoDuration,
      },
    });
  } catch (error) {
    console.error("Highlight error:", error);
  }
}

// ============================================================
// UTILITY
// ============================================================

function escapeHtml(text) {
  const div = document.createElement("div");
  div.textContent = text || "";
  return div.innerHTML;
}

/**
 * Renders the small subset of inline formatting commonly present in subtitle
 * tracks and model translations. Everything is escaped first; only exact,
 * attribute-free allowlisted tags are restored as markup afterwards.
 */
function renderSubtitleInlineMarkup(text) {
  return escapeHtml(text).replace(
    /&lt;(\/?)(i|em|b|strong|u)&gt;|&lt;br(?:\s*\/)?&gt;/gi,
    (_match, closing, tagName) =>
      tagName ? `<${closing}${tagName.toLowerCase()}>` : "<br>",
  );
}

async function copyToClipboard(text) {
  try {
    await navigator.clipboard.writeText(text);
    return true;
  } catch (error) {
    console.error("Copy failed:", error);
    return false;
  }
}

async function copyToClipboardWithFeedback(text, buttonId) {
  const btn = document.getElementById(buttonId);
  const original = btn.textContent;

  const success = await copyToClipboard(text);
  if (success) {
    btn.textContent = "Copied";
    setTimeout(() => {
      btn.textContent = original;
    }, 2000);
  }
}

function downloadTextFile(text, filename, mimeType = "text/plain") {
  const blob = new Blob([text], { type: mimeType });
  const url = URL.createObjectURL(blob);
  const a = document.createElement("a");
  a.href = url;
  a.download = filename;
  a.click();
  URL.revokeObjectURL(url);
}

function sanitizeFilename(str) {
  // 只去掉文件名真正不允许的字符 —— 旧版用 [^\w\s-] 会把中文标题整个删空
  return (
    (str || "untitled")
      .replace(/[\\/:*?"<>|\r\n\t]/g, "")
      .replace(/\s+/g, " ")
      .trim()
      .substring(0, 60) || "untitled"
  );
}

/** Seconds -> SRT timestamp, e.g. 92.5 -> "00:01:32,500" */
function srtTime(totalSeconds) {
  const ms = Math.max(0, Math.round((Number(totalSeconds) || 0) * 1000));
  const pad = (value, width = 2) => String(value).padStart(width, "0");
  return (
    `${pad(Math.floor(ms / 3600000))}:` +
    `${pad(Math.floor((ms % 3600000) / 60000))}:` +
    `${pad(Math.floor((ms % 60000) / 1000))},` +
    `${pad(ms % 1000, 3)}`
  );
}

/** The subtitle line(s) for one segment, honouring the current language mode. */
function segmentSubtitleText(segment) {
  const original = stripHtmlToText(segment.text);
  if (currentTranscriptMode === "original") return original;

  const translated = transcriptParagraphCache.get(
    transcriptTranslationCacheKey(segment),
  );
  const translation = stripHtmlToText(translated);
  if (currentTranscriptMode === "zh") return translation || original;
  return translation ? `${original}\n${translation}` : original;
}

/**
 * Exports the transcript as a real .srt file. This is how you get subtitles
 * for videos YouTube has no captions for: the panel's transcript comes from
 * Supadata, not from YouTube captions, so it exists even when no .srt can be
 * downloaded. Drop the file next to the video in source/<video>/ and clip.sh
 * or ffmpeg can use it.
 */
function exportTranscriptSrt() {
  const btn = document.getElementById("exportSrtBtn");
  const flash = (text) => {
    if (!btn) return;
    const original = btn.textContent;
    btn.textContent = text;
    setTimeout(() => {
      btn.textContent = original;
    }, 2000);
  };

  const segments = getActiveTranscriptSegments();
  if (segments.length === 0) {
    flash("No transcript");
    return;
  }

  const blocks = segments.map((segment, index) => {
    const start = Number(segment.start) || 0;
    const next = segments[index + 1];
    // Segment durations aren't kept, so run until the next one starts.
    const end = next
      ? Math.max(Number(next.start) || start + 5, start + 0.5)
      : start + 5;
    return [
      index + 1,
      `${srtTime(start)} --> ${srtTime(end)}`,
      segmentSubtitleText(segment),
      "",
    ].join("\n");
  });

  downloadTextFile(
    blocks.join("\n"),
    `${sanitizeFilename(currentVideoTitle)} [${currentVideoId}].srt`,
    "text/plain;charset=utf-8",
  );
  flash("Exported");
}

// ============================================================
// TEXT SELECTION ACTIONS
// ============================================================

/**
 * Hides actions that belong only to a live transcript selection. Clearing the
 * browser range also prevents the toolbar from returning on another tab.
 */
function dismissSelectionActions(clearSelection = false) {
  const tooltip = document.getElementById("explainTooltip");
  if (tooltip) tooltip.style.display = "none";
  if (clearSelection) window.getSelection()?.removeAllRanges();
}

/**
 * Sets up text selection handling in the transcript.
 * When the user selects text, shows Explain and Note actions.
 */
function setupExplainFeature() {
  const transcriptList = document.getElementById("transcriptList");
  if (!transcriptList) return;

  // This setup can run again after a cached transcript render. Abort old
  // document listeners so one selection creates only one action toolbar.
  selectionActionsController?.abort();
  selectionActionsController = new AbortController();
  const selectionSignal = selectionActionsController.signal;

  // Remove existing tooltip if any
  const existingTooltip = document.getElementById("explainTooltip");
  if (existingTooltip) existingTooltip.remove();

  // Create one small toolbar for actions on the selected transcript text.
  const tooltip = document.createElement("div");
  tooltip.id = "explainTooltip";
  tooltip.className = "explain-tooltip";
  tooltip.setAttribute("role", "toolbar");
  tooltip.setAttribute("aria-label", "Selected transcript actions");
  tooltip.innerHTML = `
    <button class="explain-btn" type="button">Explain</button>
    <button class="selection-note-btn" type="button">Note</button>
    <button class="selection-copy-quote-btn" type="button">Copy quote</button>
  `;
  tooltip.style.display = "none";
  document.body.appendChild(tooltip);

  let selectedText = "";
  let selectedTimestamp = 0;
  let selectedSegmentId = "";

  // Interacting with either action must preserve the transcript selection and
  // stay isolated from document and row click behavior.
  tooltip.addEventListener("mousedown", (event) => {
    event.preventDefault();
    event.stopPropagation();
  });
  tooltip.addEventListener("mouseup", (event) => {
    event.stopPropagation();
  });
  tooltip.addEventListener("click", (event) => {
    event.stopPropagation();
  });

  // Listen for text selection
  document.addEventListener(
    "mouseup",
    () => {
      const selection = window.getSelection();
      const text = selection?.toString().trim() || "";
      const range = selection?.rangeCount ? selection.getRangeAt(0) : null;

      // Both ends must be inside the transcript. The first selected row
      // supplies the timestamp when the selection spans more than one row.
      const isInTranscript = Boolean(
        range &&
          transcriptList.contains(range.startContainer) &&
          transcriptList.contains(range.endContainer),
      );

      // Allow any selection length.
      if (text.length > 0 && isInTranscript) {
        selectedText = text;
        const startElement =
          range.startContainer.nodeType === 1
            ? range.startContainer
            : range.startContainer.parentElement;
        const selectedRow = startElement?.closest(".transcript-entry");
        const rowSeconds = Number(selectedRow?.dataset.seconds);
        selectedTimestamp = Number.isFinite(rowSeconds) ? rowSeconds : 0;
        selectedSegmentId = selectedRow?.dataset.segmentId || "";

        // Set the final coordinates while the toolbar is still hidden. If it
        // becomes visible first, Chrome paints it at its default left edge for
        // one frame before moving it to the selection center.
        const rect = range.getBoundingClientRect();
        tooltip.style.top = `${rect.bottom + window.scrollY + 8}px`;
        tooltip.style.left = `${rect.left + rect.width / 2}px`;
        tooltip.style.display = "flex";
      } else {
        tooltip.style.display = "none";
      }
    },
    { signal: selectionSignal },
  );

  // Hide tooltip when clicking elsewhere
  document.addEventListener(
    "mousedown",
    (event) => {
      if (!tooltip.contains(event.target)) {
        tooltip.style.display = "none";
      }
    },
    { signal: selectionSignal },
  );

  // Handle explain button click
  tooltip
    .querySelector(".explain-btn")
    .addEventListener("click", async (event) => {
      event.preventDefault();
      event.stopPropagation();
      if (!selectedText) return;

      tooltip.style.display = "none";
      await showExplanation(selectedText);
    });

  // Save the exact selected words at the first selected transcript row. This
  // action does not move playback and does not ask the AI to rewrite the text.
  tooltip
    .querySelector(".selection-note-btn")
    .addEventListener("click", async (event) => {
      event.preventDefault();
      event.stopPropagation();
      if (!selectedText || !currentVideoId) return;

      const button = event.currentTarget;
      const originalText = button.textContent;
      button.textContent = "Saving...";
      button.disabled = true;

      try {
        const result = await chrome.runtime.sendMessage({
          action: "saveNote",
          videoId: currentVideoId,
          timestamp: selectedTimestamp,
          videoTitle: currentVideoTitle,
          channelName: currentChannelName,
          selectedText,
        });

        if (!result?.success) {
          throw new Error(result?.error || "Could not save note");
        }

        button.textContent = "Saved";
        loadNotes(currentVideoId);
        setTimeout(() => {
          tooltip.style.display = "none";
          button.textContent = originalText;
          button.disabled = false;
        }, 900);
      } catch (error) {
        console.error("[YouTube Digest] Save selected note error:", error);
        button.textContent = "Error";
        setTimeout(() => {
          button.textContent = originalText;
          button.disabled = false;
        }, 1500);
      }
    });

  // 复制引用块：原文 + 译文（只取缓存里已有的）+ 出处 + 时间戳深链。
  // 零 AI 调用、零额度 —— 译文不在缓存里就不带，绝不为此触发翻译。
  tooltip
    .querySelector(".selection-copy-quote-btn")
    .addEventListener("click", async (event) => {
      event.preventDefault();
      event.stopPropagation();
      if (!selectedText || !currentVideoId) return;

      const button = event.currentTarget;
      const originalText = button.textContent;

      const translation = collectQuoteTranslation(
        selectedText,
        selectedSegmentId,
      );
      const ok = await copyQuoteBlock(
        selectedText,
        selectedTimestamp,
        translation,
      );

      button.textContent = ok ? "Copied" : "Failed";
      tooltip.style.display = "none";
      setTimeout(() => {
        button.textContent = originalText;
      }, 1500);
    });
}

// ============================================================
// QUOTE COPY (#13)
// ============================================================

/**
 * 收集选中文字对应各句的中文译文（仅从转写译文缓存里取）。
 * 选中跨多句时从起始句往后按句累加，直到覆盖选中长度；
 * 缓存里没有的句子跳过 —— 未翻译过的内容就不带译文。
 */
function collectQuoteTranslation(selectedText, startSegmentId) {
  if (!startSegmentId) return "";
  const segments = getActiveTranscriptSegments();
  const startIdx = segments.findIndex((s) => s.id === startSegmentId);
  if (startIdx === -1) return "";
  const selLen = selectedText.replace(/\s+/g, " ").trim().length;
  const parts = [];
  let covered = 0;
  for (let i = startIdx; i < segments.length && covered < selLen + 8; i++) {
    const t = transcriptParagraphCache.get(
      transcriptTranslationCacheKey(segments[i]),
    );
    if (t) parts.push(t);
    covered += String(segments[i].text || "").replace(/\s+/g, " ").length;
  }
  return parts.join(" ");
}

/**
 * 把选中文字组装成「原文 + 译文 + 出处 + 时间戳深链」的引用块，
 * 以 text/plain + text/html 双格式写入剪贴板：
 * 粘进 Notion/飞书保留引用样式，粘进纯文本编辑器退化为 Markdown 引用。
 */
async function copyQuoteBlock(text, seconds, translation) {
  const url =
    currentVideoUrl || `https://www.youtube.com/watch?v=${currentVideoId}`;
  const link = noteWithTs(url, seconds);
  const title = currentVideoTitle || currentVideoId;
  const source = currentChannelName ? `${title} · ${currentChannelName}` : title;

  const plainLines = [`> ${text}`];
  if (translation) plainLines.push(`> ${translation}`);
  plainLines.push(">", `> —— [${source}](${link})`);
  const plain = plainLines.join("\n");

  const htmlParts = [`<p>${escapeHtml(text)}</p>`];
  if (translation) htmlParts.push(`<p>${escapeHtml(translation)}</p>`);
  htmlParts.push(
    `<p>— <a href="${escapeHtml(link)}">${escapeHtml(source)}</a></p>`,
  );
  const html = `<blockquote>${htmlParts.join("")}</blockquote>`;

  if (typeof ClipboardItem === "function" && navigator.clipboard?.write) {
    try {
      await navigator.clipboard.write([
        new ClipboardItem({
          "text/plain": new Blob([plain], { type: "text/plain" }),
          "text/html": new Blob([html], { type: "text/html" }),
        }),
      ]);
      return true;
    } catch (_error) {
      // 富文本写入失败时退到纯文本
    }
  }
  try {
    await navigator.clipboard.writeText(plain);
    return true;
  } catch (_error) {
    return false;
  }
}

// ============================================================
// QUOTE CARD (#14) —— canvas 本地渲染金句卡片，零 AI 消耗
// ============================================================

// 九个厂商主题模板。三种布局基底：
//   quote     深色引言卡（大引号 + 白字，传播样式）
//   editorial 暖纸编辑部风（衬线 + 米白底，编辑感）
//   split     双语对照（上原文下译文，强调色分隔条）
const QUOTE_CARD_TEMPLATES = [
  {
    id: "claude",
    label: "Claude",
    layout: "editorial",
    bg: "#F0EEE6",
    bg2: null,
    text: "#3D3929",
    sub: "#87867F",
    accent: "#D97757",
    serif: true,
  },
  {
    id: "openai",
    label: "OpenAI",
    layout: "quote",
    bg: "#0F0F0F",
    bg2: null,
    text: "#ECECEC",
    sub: "#8A8A8A",
    accent: "#10A37F",
    serif: false,
  },
  {
    id: "gemini",
    label: "Gemini",
    layout: "quote",
    bg: "#0B1E3F",
    bg2: "#3A2E6E",
    text: "#F2F5FF",
    sub: "#9AA8CE",
    accent: "#8AB4F8",
    serif: false,
  },
  {
    id: "grok",
    label: "Grok",
    layout: "quote",
    bg: "#000000",
    bg2: null,
    text: "#FFFFFF",
    sub: "#9CA3AF",
    accent: "#E5E7EB",
    serif: false,
  },
  {
    id: "deepseek",
    label: "DeepSeek",
    layout: "quote",
    bg: "#101426",
    bg2: null,
    text: "#E6E9F5",
    sub: "#8B93B5",
    accent: "#4D6BFE",
    serif: false,
  },
  {
    id: "kimi",
    label: "Kimi",
    layout: "quote",
    bg: "#12122A",
    bg2: null,
    text: "#EDEDF7",
    sub: "#9C9CC4",
    accent: "#6C7BFF",
    serif: false,
  },
  {
    id: "glm",
    label: "GLM",
    layout: "split",
    bg: "#F5F7FF",
    bg2: null,
    text: "#1A1F36",
    sub: "#6B7394",
    accent: "#3859FF",
    serif: false,
  },
  {
    id: "tencent",
    label: "Tencent",
    layout: "split",
    bg: "#F2F6FC",
    bg2: null,
    text: "#17233D",
    sub: "#6B7B99",
    accent: "#0052D9",
    serif: false,
  },
  {
    id: "alibaba",
    label: "Alibaba",
    layout: "editorial",
    bg: "#FFF8F1",
    bg2: null,
    text: "#2B1D12",
    sub: "#9C8776",
    accent: "#FF6A00",
    serif: true,
  },
];

const QUOTE_CARD_STORAGE_KEY = "ytd_quote_card_template";
const QUOTE_CARD_WIDTH = 1080;
const QUOTE_CARD_HEIGHT = 1440;
const QUOTE_CARD_PADDING = 96;

const quoteCardFontStack = (serif) =>
  serif
    ? '"Georgia", "Songti SC", "SimSun", serif'
    : '"-apple-system", "Segoe UI", "PingFang SC", "Microsoft YaHei", sans-serif';

/** 按词断行，超长词按字符再拆（中英混排都能正确折行）。 */
function wrapCanvasText(ctx, text, maxWidth) {
  const lines = [];
  let line = "";
  const pushLine = () => {
    if (line) lines.push(line);
    line = "";
  };
  for (const word of String(text).replace(/\s+/g, " ").trim().split(" ")) {
    let chunk = word;
    while (ctx.measureText(line ? `${line} ${chunk}` : chunk).width > maxWidth) {
      if (line && ctx.measureText(`${line} ${chunk}`).width > maxWidth) {
        // 先看整词能否另起一行
        if (line) {
          pushLine();
          continue;
        }
      }
      // 单词本身超宽：按字符切
      if (!line && ctx.measureText(chunk).width > maxWidth) {
        let piece = "";
        for (const ch of chunk) {
          if (ctx.measureText(piece + ch).width > maxWidth && piece) {
            lines.push(piece);
            piece = ch;
          } else {
            piece += ch;
          }
        }
        chunk = piece;
        if (!chunk) break;
        continue;
      }
      break;
    }
    if (!chunk) continue;
    const candidate = line ? `${line} ${chunk}` : chunk;
    if (ctx.measureText(candidate).width <= maxWidth) {
      line = candidate;
    } else {
      pushLine();
      line = chunk;
    }
  }
  pushLine();
  return lines;
}

/** 原文很长时自动缩字号；min 字号仍放不下则截行加省略号，保证不越过边界。 */
function fitCanvasFontSize(
  ctx,
  text,
  maxWidth,
  maxHeight,
  start,
  min,
  lineHeight,
  fontStack,
) {
  const family = fontStack || quoteCardFontStack(false);
  let size = start;
  for (; size >= min; size -= 4) {
    ctx.font = `${size}px ${family}`;
    const lines = wrapCanvasText(ctx, text, maxWidth);
    if (lines.length * size * lineHeight <= maxHeight) return { size, lines };
  }
  ctx.font = `${min}px ${family}`;
  const lines = wrapCanvasText(ctx, text, maxWidth);
  const maxLines = Math.max(1, Math.floor(maxHeight / (min * lineHeight)));
  if (lines.length > maxLines) {
    lines.length = maxLines;
    lines[maxLines - 1] = lines[maxLines - 1].replace(/[\s,.;:，。！？；]*$/, "…");
  }
  return { size: min, lines };
}

function drawQuoteCard(canvas, template, quote, translation, meta) {
  canvas.width = QUOTE_CARD_WIDTH;
  canvas.height = QUOTE_CARD_HEIGHT;
  const ctx = canvas.getContext("2d");
  const { layout, bg, bg2, text, sub, accent, serif } = template;
  const inner = QUOTE_CARD_WIDTH - QUOTE_CARD_PADDING * 2;

  // 背景：纯色或垂直渐变
  if (bg2) {
    const grad = ctx.createLinearGradient(0, 0, 0, QUOTE_CARD_HEIGHT);
    grad.addColorStop(0, bg);
    grad.addColorStop(1, bg2);
    ctx.fillStyle = grad;
  } else {
    ctx.fillStyle = bg;
  }
  ctx.fillRect(0, 0, QUOTE_CARD_WIDTH, QUOTE_CARD_HEIGHT);

  // 顶部：模板名 + 强调色短线
  ctx.textBaseline = "alphabetic";
  ctx.fillStyle = accent;
  ctx.fillRect(QUOTE_CARD_PADDING, QUOTE_CARD_PADDING - 24, 56, 8);
  ctx.fillStyle = sub;
  ctx.font = `600 26px ${quoteCardFontStack(false)}`;
  ctx.fillText(template.label.toUpperCase(), QUOTE_CARD_PADDING, QUOTE_CARD_PADDING + 28);

  const contentTop = QUOTE_CARD_PADDING + 120;
  const footerTop = QUOTE_CARD_HEIGHT - QUOTE_CARD_PADDING - 96;
  const contentHeight = footerTop - contentTop;
  const bodyWidth = inner;

  if (layout === "split") {
    // ---- 双语对照：上原文 / 强调色分隔条 / 下译文 ----
    const half = (contentHeight - 24) / 2;
    const q = fitCanvasFontSize(
      ctx,
      quote.quote,
      bodyWidth,
      half,
      76,
      44,
      1.4,
      quoteCardFontStack(serif),
    );
    ctx.fillStyle = text;
    ctx.font = `${q.size}px ${quoteCardFontStack(serif)}`;
    let y = contentTop + q.size;
    for (const line of q.lines) {
      ctx.fillText(line, QUOTE_CARD_PADDING, y);
      y += q.size * 1.4;
    }
    ctx.fillStyle = accent;
    ctx.fillRect(QUOTE_CARD_PADDING, contentTop + half + 2, inner, 14);
    if (translation) {
      const t = fitCanvasFontSize(
        ctx,
        translation,
        bodyWidth,
        half - 104,
        64,
        38,
        1.5,
        quoteCardFontStack(false),
      );
      ctx.fillStyle = text;
      ctx.font = `${t.size}px ${quoteCardFontStack(false)}`;
      y = contentTop + half + 24 + t.size + 40;
      for (const line of t.lines) {
        ctx.fillText(line, QUOTE_CARD_PADDING, y);
        y += t.size * 1.5;
      }
    }
  } else {
    // ---- quote / editorial：大引号 + 原文 + 译文小字 ----
    const markSize = layout === "editorial" ? 200 : 160;
    ctx.fillStyle = accent;
    ctx.font = `700 ${markSize}px ${quoteCardFontStack(true)}`;
    ctx.fillText("\u201C", QUOTE_CARD_PADDING - 10, contentTop + markSize * 0.55);

    const quoteTop = contentTop + markSize * 0.45;
    const quoteFont = quoteCardFontStack(serif);

    // 垂直流布局：先给译文定占位（最多 4 行），原文在剩余空间里缩字号，
    // 译文紧随原文之后 —— 两块内容共用一条向下的流，绝不重叠
    let tLines = [];
    let tSize = 0;
    if (translation) {
      for (const s of [42, 34]) {
        ctx.font = `${s}px ${quoteCardFontStack(false)}`;
        const wrapped = wrapCanvasText(ctx, translation, bodyWidth);
        tSize = s;
        tLines = wrapped.slice(0, 4);
        if (wrapped.length <= 4) break;
      }
    }

    // 原文最后一个 baseline 的上限：译文块 + 底栏各留安全距
    const maxY = tLines.length
      ? footerTop - 56 - tSize * (1 + 1.6 * (tLines.length - 1)) - 72
      : footerTop - 72;
    const q = fitCanvasFontSize(
      ctx,
      quote.quote,
      bodyWidth,
      maxY - quoteTop,
      84,
      36,
      1.4,
      quoteFont,
    );
    ctx.fillStyle = text;
    ctx.font = `${q.size}px ${quoteFont}`;
    let y = quoteTop + q.size;
    for (const line of q.lines) {
      ctx.fillText(line, QUOTE_CARD_PADDING, y);
      y += q.size * 1.4;
    }
    if (tLines.length) {
      let ty = y - q.size * 1.4 + 48 + tSize;
      ctx.fillStyle = sub;
      ctx.font = `${tSize}px ${quoteCardFontStack(false)}`;
      for (const line of tLines) {
        ctx.fillText(line, QUOTE_CARD_PADDING, ty);
        ty += tSize * 1.6;
      }
    }
  }

  // ---- 底栏：细线 + 出处 + 时间戳 ----
  ctx.fillStyle = sub;
  ctx.globalAlpha = 0.5;
  ctx.fillRect(QUOTE_CARD_PADDING, footerTop - 44, inner, 2);
  ctx.globalAlpha = 1;
  ctx.font = `500 30px ${quoteCardFontStack(false)}`;
  const titleLine = meta.title.length > 46 ? `${meta.title.slice(0, 45)}…` : meta.title;
  ctx.fillText(titleLine, QUOTE_CARD_PADDING, footerTop + 12);
  ctx.fillStyle = accent;
  ctx.font = `600 28px ${quoteCardFontStack(false)}`;
  const byline = [meta.timestamp, meta.channel].filter(Boolean).join(" · ");
  ctx.fillText(byline, QUOTE_CARD_PADDING, footerTop + 64);
}

function quoteCardTemplate() {
  const id = localStorage.getItem(QUOTE_CARD_STORAGE_KEY);
  return (
    QUOTE_CARD_TEMPLATES.find((t) => t.id === id) || QUOTE_CARD_TEMPLATES[0]
  );
}

// ============================================================
// TIMELINE HEATMAP (#17) —— 转写顶部的时间带导航
// 三层着色：底色（普通）/ keyMoments（关键点加深）/ 笔记（最深+圆点），
// 章节边界做浮层（名字进悬停 tooltip，窄段不渲染文字），
// 悬停限宽 tooltip 预览首句，点击 seekTo 并滚动转写。
// 块粒度自适应侧边栏宽度（每桶 ≥8px），纯本地数据渲染，零 AI 消耗。
// ============================================================

let timelineRenderSignature = "";
let timelineResizeObserver = null;
let timelinePlayheadSeconds = 0;

function timelineDuration() {
  if (currentVideoDuration) return Number(currentVideoDuration);
  const segments = getActiveTranscriptSegments();
  return segments.length
    ? Number(segments[segments.length - 1].start) + 60
    : 0;
}

/** 找到时间点所在（或之前最近）的转写分段，取首句做 tooltip 预览。 */
function timelineSegmentAt(seconds) {
  const segments = getActiveTranscriptSegments();
  if (!segments.length) return null;
  let found = segments[0];
  for (const segment of segments) {
    if (Number(segment.start) <= seconds) found = segment;
    else break;
  }
  return found;
}

function renderTimelineHeatmap(force = false) {
  const host = document.getElementById("timelineHeatmap");
  if (!host) return;
  const duration = timelineDuration();
  if (!duration || !currentTranscript?.length) {
    host.style.display = "none";
    return;
  }
  host.style.display = "block";

  const width = host.clientWidth || 300;
  const keyMoments = (currentAnalysis?.keyMoments || []).map(Number);
  const notesForVideo = currentNotes || [];
  const noteTimes = notesForVideo.map((n) => Number(n.timestampSeconds) || 0);
  const chapters = currentAnalysis?.chapters || [];

  const signature = [
    duration,
    width,
    keyMoments.length,
    noteTimes.length,
    chapters.length,
    currentVideoId,
    currentTranscriptMode,
  ].join("|");
  if (!force && signature === timelineRenderSignature) return;
  timelineRenderSignature = signature;

  // 自适应分桶：每桶 ≥8px，≥12 桶且每桶 ≥10 秒，避免长视频桶过窄
  const bucketCount = Math.max(
    12,
    Math.min(Math.floor(width / 8), Math.ceil(duration / 10)),
  );
  const bucketSeconds = duration / bucketCount;
  const buckets = [];
  for (let i = 0; i < bucketCount; i++) {
    const from = i * bucketSeconds;
    const to = from + bucketSeconds;
    const km = keyMoments.filter((t) => t >= from && t < to).length;
    const nt = noteTimes.filter((t) => t >= from && t < to).length;
    buckets.push({ from, to, km, nt });
  }

  host.innerHTML = "";

  // ---- 热力带 ----
  const heat = document.createElement("div");
  heat.className = "timeline-heat";
  buckets.forEach((bucket) => {
    const cell = document.createElement("div");
    const level = bucket.nt > 0 ? 2 : bucket.km > 0 ? 1 : 0;
    cell.className = `timeline-cell level-${level}`;
    cell.dataset.from = bucket.from;
    cell.dataset.to = bucket.to;
    if (bucket.nt > 0) cell.classList.add("has-note");
    heat.appendChild(cell);
  });
  host.appendChild(heat);

  // ---- 章节浮层（只画边界分隔，名字进 tooltip） ----
  if (chapters.length > 0) {
    const layer = document.createElement("div");
    layer.className = "timeline-chapters";
    chapters.forEach((chapter, index) => {
      const from = Number(chapter.timestampSeconds) || 0;
      const to = Number(chapters[index + 1]?.timestampSeconds) || duration;
      if (to <= from) return;
      const segment = document.createElement("div");
      segment.className = "timeline-chapter";
      segment.style.left = `${(from / duration) * 100}%`;
      segment.style.width = `${((to - from) / duration) * 100}%`;
      segment.dataset.chapterTitle = chapter.title || "";
      segment.dataset.chapterTime = noteClock(from);
      layer.appendChild(segment);
    });
    host.appendChild(layer);
  }

  // ---- 笔记标记点 ----
  const dots = document.createElement("div");
  dots.className = "timeline-dots";
  noteTimes.forEach((t) => {
    if (t <= 0 || t >= duration) return;
    const dot = document.createElement("div");
    dot.className = "timeline-dot";
    dot.style.left = `${(t / duration) * 100}%`;
    dots.appendChild(dot);
  });
  host.appendChild(dots);

  // ---- 播放位置指针 ----
  const playhead = document.createElement("div");
  playhead.className = "timeline-playhead";
  playhead.id = "timelinePlayhead";
  host.appendChild(playhead);

  // ---- 悬停 tooltip（单个复用） ----
  const tip = document.createElement("div");
  tip.className = "timeline-tip";
  tip.style.display = "none";
  host.appendChild(tip);

  // ---- 事件（on* 赋值：DOM 重建时自动覆盖，无重复绑定） ----
  host.onmousemove = (event) => {
    const cell = event.target.closest(".timeline-cell");
    const chapter = event.target.closest(".timeline-chapter");
    const rows = [];
    if (chapter) {
      rows.push(
        `${chapter.dataset.chapterTime || ""} ${chapter.dataset.chapterTitle || ""}`.trim(),
      );
    }
    if (cell) {
      const from = Number(cell.dataset.from) || 0;
      const to = Number(cell.dataset.to) || 0;
      const segment = timelineSegmentAt(from + 1);
      const kind =
        cell.classList.contains("has-note")
          ? "note"
          : cell.classList.contains("level-1")
            ? "key"
            : "";
      const kindLabel =
        kind === "note" ? "· 有笔记" : kind === "key" ? "· 关键点" : "";
      rows.push(`${noteClock(from)} – ${noteClock(to)} ${kindLabel}`.trim());
      const first = segment ? stripHtmlToText(segment.text) : "";
      if (first) rows.push(first);
      // 译文：只取已翻译缓存（双语/中文模式下翻过的句子），绝不触发 AI
      const translated = segment
        ? transcriptParagraphCache.get(transcriptTranslationCacheKey(segment))
        : null;
      if (translated) rows.push(stripHtmlToText(translated));
    }
    if (rows.length === 0) {
      tip.style.display = "none";
      return;
    }
    tip.innerHTML = rows
      .map((row, i) => `<div class="${i === 0 ? "tip-head" : ""}">${escapeHtml(row)}</div>`)
      .join("");
    tip.style.display = "block";
    // 跟随鼠标但夹在容器内
    const hostRect = host.getBoundingClientRect();
    const x = Math.min(
      Math.max(event.clientX - hostRect.left, 8),
      hostRect.width - tip.offsetWidth - 8,
    );
    tip.style.left = `${x}px`;
  };
  host.onmouseleave = () => {
    tip.style.display = "none";
  };
  host.onclick = (event) => {
    const cell = event.target.closest(".timeline-cell");
    if (!cell) return;
    const from = Number(cell.dataset.from) || 0;
    void seekTo(Math.round(from + 1));
    // 立即把转写滚到目标处（tick 高亮随后跟上）
    const seconds = from + 1;
    const segments = getActiveTranscriptSegments();
    let target = null;
    for (const segment of segments) {
      if (Number(segment.start) <= seconds) target = segment;
      else break;
    }
    if (target?.id) {
      document
        .querySelector(
          `#transcriptList .transcript-entry[data-segment-id="${CSS.escape(target.id)}"]`,
        )
        ?.scrollIntoView({ behavior: "smooth", block: "start" });
    }
  };

  // ---- 侧边栏拖宽/变窄时自适应重渲染 ----
  if (!timelineResizeObserver) {
    timelineResizeObserver = new ResizeObserver(() => {
      renderTimelineHeatmap(true);
    });
    timelineResizeObserver.observe(host);
  }

  updateTimelinePlayhead(null);
}

/** 播放指针同步。seconds 为 null 时按最后已知位置刷新（重渲染后不丢位）。 */
function updateTimelinePlayhead(seconds) {
  const playhead = document.getElementById("timelinePlayhead");
  if (!playhead) return;
  const duration = timelineDuration();
  if (!duration) return;
  const at =
    typeof seconds === "number" ? seconds : timelinePlayheadSeconds;
  timelinePlayheadSeconds = at;
  playhead.style.display = "block";
  playhead.style.left = `${Math.min(100, (at / duration) * 100)}%`;
}

/** 打开卡片预览弹窗：canvas 实时预览 + 模板横排切换 + 下载 PNG。 */
function openQuoteCardModal(quote, index) {
  document.getElementById("quoteCardModal")?.remove();

  const translation = getInterfaceTranslation(
    "overview",
    `quote-${index}`,
    quote.quote,
  );
  const meta = {
    title: currentVideoTitle || currentVideoId || "YouTube",
    channel: currentChannelName || "",
    timestamp: quote.timestamp || noteClock(quote.timestampSeconds),
  };

  const overlay = document.createElement("div");
  overlay.id = "quoteCardModal";
  overlay.className = "quote-card-overlay";
  overlay.innerHTML = `
    <div class="quote-card-panel">
      <div class="quote-card-preview"><canvas aria-label="Quote card preview"></canvas></div>
      <div class="quote-card-templates" role="listbox" aria-label="Card template"></div>
      <div class="quote-card-footer">
        <button class="quote-card-download" type="button">Download PNG</button>
        <button class="quote-card-close" type="button">Close</button>
      </div>
    </div>
  `;
  document.body.appendChild(overlay);

  const canvas = overlay.querySelector("canvas");
  let template = quoteCardTemplate();

  const draw = () => drawQuoteCard(canvas, template, quote, translation, meta);

  const chips = overlay.querySelector(".quote-card-templates");
  QUOTE_CARD_TEMPLATES.forEach((t) => {
    const chip = document.createElement("button");
    chip.type = "button";
    chip.className = "quote-card-chip";
    chip.textContent = t.label;
    chip.setAttribute("role", "option");
    chip.style.setProperty("--chip-accent", t.accent);
    if (t.id === template.id) chip.classList.add("active");
    chip.addEventListener("click", () => {
      template = t;
      localStorage.setItem(QUOTE_CARD_STORAGE_KEY, t.id);
      chips
        .querySelectorAll(".quote-card-chip")
        .forEach((c) => c.classList.remove("active"));
      chip.classList.add("active");
      draw();
    });
    chips.appendChild(chip);
  });

  overlay.querySelector(".quote-card-close").addEventListener("click", () => {
    overlay.remove();
  });
  overlay.addEventListener("click", (e) => {
    if (e.target === overlay) overlay.remove();
  });

  overlay
    .querySelector(".quote-card-download")
    .addEventListener("click", () => {
      canvas.toBlob((blob) => {
        if (!blob) return;
        const url = URL.createObjectURL(blob);
        const a = document.createElement("a");
        a.href = url;
        a.download = `quote-${template.id}-${Math.floor(
          Number(quote.timestampSeconds) || 0,
        )}s.png`;
        a.click();
        setTimeout(() => URL.revokeObjectURL(url), 1000);
      }, "image/png");
    });

  draw();
}

/**
 * Shows the explanation modal and fetches it from the configured AI provider.
 */
async function showExplanation(selectedText) {
  // Create modal
  const modal = document.createElement("div");
  modal.id = "explainModal";
  modal.className = "explain-modal-overlay";
  modal.innerHTML = `
    <div class="explain-modal">
      <div class="explain-modal-header">
        <div class="explain-modal-title">Explain</div>
        <button class="explain-modal-close" id="closeExplain">Close</button>
      </div>
      <div class="explain-selected-text">"${escapeHtml(selectedText.substring(0, 200))}${selectedText.length > 200 ? "..." : ""}"</div>
      <div class="explain-modal-content" id="explanationContent">
        <div class="explain-loading">
          <div class="loading-bar"></div>
          <span>Analyzing...</span>
        </div>
      </div>
    </div>
  `;

  document.body.appendChild(modal);

  // Close handlers
  document
    .getElementById("closeExplain")
    .addEventListener("click", () => modal.remove());
  modal.addEventListener("click", (e) => {
    if (e.target === modal) modal.remove();
  });

  // Get some context around the selection from the transcript
  const transcriptContext = getTranscriptContext(selectedText);

  // Fetch explanation
  try {
    const result = await chrome.runtime.sendMessage({
      action: "explainSelection",
      selectedText: selectedText,
      transcriptContext: transcriptContext,
      videoTitle: currentVideoTitle,
    });

    const contentDiv = document.getElementById("explanationContent");
    if (result.success) {
      contentDiv.innerHTML = `<div class="explain-text">${escapeHtml(result.explanation).replace(/\n\n/g, "</p><p>").replace(/\n/g, "<br>")}</div>`;
    } else {
      contentDiv.innerHTML = `<div class="explain-error">Failed to get explanation: ${escapeHtml(result.error)}</div>`;
    }
  } catch (error) {
    const contentDiv = document.getElementById("explanationContent");
    contentDiv.innerHTML = `<div class="explain-error">Error: ${escapeHtml(error.message)}</div>`;
  }
}

/**
 * Gets surrounding context from the transcript for the selected text.
 */
function getTranscriptContext(selectedText) {
  const fullText = currentTranscriptText || "";
  const index = fullText.indexOf(selectedText);

  if (index === -1) return "";

  // Get 200 chars before and after
  const start = Math.max(0, index - 200);
  const end = Math.min(fullText.length, index + selectedText.length + 200);

  return fullText.substring(start, end);
}

// ============================================================
// CACHING
// ============================================================

/**
 * Saves the current digest results to persistent local storage.
 * Results survive browser restarts — reopening the same video loads from cache
 * without consuming API tokens or Supadata calls.
 * Cache expires after 30 days. Oldest entries evicted when > 20 videos cached.
 */
async function saveToCache(videoId) {
  if (!videoId || !currentTranscript) return;

  try {
    // Persist semantic-segment translations for this video.
    const paragraphCacheForVideo = {};
    for (const [key, value] of transcriptParagraphCache.entries()) {
      if (key.startsWith(`${videoId}:`)) {
        paragraphCacheForVideo[key] = value;
      }
    }
    const interfaceCacheForVideo = {};
    for (const [key, value] of interfaceTranslationCache.entries()) {
      if (key.startsWith(`${videoId}:`)) {
        interfaceCacheForVideo[key] = value;
      }
    }

    const cacheData = {
      analysis: currentAnalysis, // May be null if not yet analyzed
      transcript: currentTranscript,
      transcriptText: currentTranscriptText,
      transcriptTimestamped: currentTranscriptTimestamped,
      transcriptLanguage: currentTranscriptLanguage,
      videoTitle: currentVideoTitle,
      channelName: currentChannelName,
      paragraphCache: paragraphCacheForVideo,
      interfaceCache: interfaceCacheForVideo,
      timestamp: Date.now(),
    };

    await chrome.storage.local.set({ [`digest_${videoId}`]: cacheData });
    debugLog(
      "Saved to cache:",
      videoId,
      currentAnalysis ? "(with analysis)" : "(transcript only)",
    );

    // Evict old entries if we have more than 20 videos cached
    await evictOldCacheEntries(20);
  } catch (error) {
    console.error("Cache save error:", error);
  }
}

/**
 * Keeps the cache from growing unbounded.
 * Removes the oldest entries when we exceed maxEntries videos.
 *
 * @param {number} maxEntries - Maximum number of cached videos to keep
 */
async function evictOldCacheEntries(maxEntries) {
  try {
    const allData = await chrome.storage.local.get(null);
    let digestKeys = Object.keys(allData).filter((k) =>
      k.startsWith("digest_"),
    );
    const THIRTY_DAYS = 30 * 24 * 60 * 60 * 1000;
    const expired = digestKeys.filter((key) => {
      const timestamp = Number(allData[key]?.timestamp) || 0;
      return Date.now() - timestamp > THIRTY_DAYS;
    });
    if (expired.length) {
      await chrome.storage.local.remove(expired);
      const expiredSet = new Set(expired);
      digestKeys = digestKeys.filter((key) => !expiredSet.has(key));
    }

    if (digestKeys.length <= maxEntries) return;

    // Sort by timestamp (oldest first) and remove excess
    const sorted = digestKeys
      .map((k) => ({ key: k, ts: allData[k]?.timestamp || 0 }))
      .sort((a, b) => a.ts - b.ts);

    const toRemove = sorted
      .slice(0, sorted.length - maxEntries)
      .map((e) => e.key);
    if (toRemove.length > 0) {
      await chrome.storage.local.remove(toRemove);
      debugLog(`[YouTube Digest] Evicted ${toRemove.length} old cache entries`);
    }
  } catch (error) {
    console.error("Cache eviction error:", error);
  }
}

/**
 * Loads digest results from persistent local storage.
 * Returns null if not cached or expired (30-day expiry).
 */
async function loadFromCache(videoId) {
  if (!videoId) return null;

  try {
    const result = await chrome.storage.local.get(`digest_${videoId}`);
    const cached = result[`digest_${videoId}`];

    if (!cached) return null;

    // Cache expires after 30 days
    const THIRTY_DAYS = 30 * 24 * 60 * 60 * 1000;
    if (Date.now() - cached.timestamp > THIRTY_DAYS) {
      await chrome.storage.local.remove(`digest_${videoId}`);
      return null;
    }

    return cached;
  } catch (error) {
    console.error("Cache load error:", error);
    return null;
  }
}

/**
 * Updates the cache after enhance or translation operations.
 */
async function updateCache() {
  if (currentVideoId) {
    await saveToCache(currentVideoId);
  }
}

// ============================================================
// NOTES
// ============================================================

/**
 * Loads and renders notes from storage.
 * @param {string|null} videoId - Filter by video ID, or null for all notes
 */
async function loadNotes(videoId) {
  try {
    const result = await chrome.runtime.sendMessage({
      action: "getNotes",
      videoId: videoId,
    });

    if (result.success) {
      currentNotes = result.notes || [];
      currentNotesFilterVideoId = videoId;
      renderNotes(result.notes, videoId);
      renderTimelineHeatmap();
    }
  } catch (error) {
    console.error("[YouTube Digest Panel] Load notes error:", error);
  }
}

/**
 * Exports the notes of the current video as a clip list CSV, the format
 * clip.sh expects. Each note becomes one clip: it starts at the note's
 * timestamp and ends where the next note starts (capped so clips stay short).
 */
async function exportClipsCsv() {
  const btn = document.getElementById("exportClipsBtn");
  const flash = (text) => {
    if (!btn) return;
    const original = btn.textContent;
    btn.textContent = text;
    setTimeout(() => {
      btn.textContent = original;
    }, 2000);
  };

  // In "All Notes" mode currentNotes spans several videos — narrow it down.
  const videoId = currentNotesFilterVideoId || currentVideoId;
  if (!videoId) {
    flash("Open a video first");
    return;
  }

  const notes = (currentNotes || [])
    .filter((note) => note.videoId === videoId)
    .filter((note) => Number(note.timestampSeconds) > 0)
    .sort(
      (a, b) =>
        (Number(a.timestampSeconds) || 0) - (Number(b.timestampSeconds) || 0),
    );

  if (notes.length === 0) {
    flash("No notes yet");
    return;
  }

  const MAX_CLIP_SECONDS = 180;
  const rows = ["start,end,title,reason,summary"];

  notes.forEach((note, index) => {
    const start = Math.floor(Number(note.timestampSeconds) || 0);
    const next = notes[index + 1];
    let end = next
      ? Math.min(
          Math.floor(Number(next.timestampSeconds) || 0),
          start + MAX_CLIP_SECONDS,
        )
      : start + 60;
    if (end <= start) end = start + 20;

    const text = stripHtmlToText(note.text);
    const title = text.slice(0, 24) || `clip-${start}s`;
    rows.push([start, end, csvCell(title), "", csvCell(text)].join(","));
  });

  const csv = rows.join("\n");

  // 首选：通过 native host 直接写进 source/<视频>/clips.csv，不经下载文件夹
  if (await saveClipListNatively(videoId, csv)) {
    flash(`Saved ${notes.length}`);
    return;
  }

  // 兜底：浏览器下载（没装 native host，或视频还没下载到本地）
  downloadTextFile(csv, `clips-${videoId}.csv`, "text/csv;charset=utf-8");
  flash(`Exported ${notes.length}`);
}

/**
 * Tries to write the clip list straight into the video's local folder via the
 * native host. Returns true if that worked; falls back to a browser download
 * when the host is missing or the video hasn't been downloaded yet.
 */
async function saveClipListNatively(videoId, csv) {
  try {
    const res = await chrome.runtime.sendMessage({
      action: "saveClipList",
      videoId,
      content: csv,
    });
    return !!res?.success;
  } catch (_error) {
    return false;
  }
}

// ============================================================
// OBSIDIAN EXPORT
// ============================================================

/** Seconds -> M:SS / H:MM:SS clock, for display inside the note. */
function noteClock(total) {
  const s = Math.max(0, Math.floor(Number(total) || 0));
  const h = Math.floor(s / 3600);
  const m = Math.floor((s % 3600) / 60);
  const ss = String(s % 60).padStart(2, "0");
  const mm = String(m).padStart(2, "0");
  return h ? `${h}:${mm}:${ss}` : `${m}:${ss}`;
}

/** Seconds -> YouTube deep-link t= param, e.g. 83 -> "t=1m23s". */
function noteTParam(total) {
  const s = Math.max(0, Math.floor(Number(total) || 0));
  return `t=${Math.floor(s / 60)}m${s % 60}s`;
}

/** Appends the timestamp param to a YouTube URL regardless of ?/& state. */
function noteWithTs(url, seconds) {
  const sep = url.includes("?") ? "&" : "?";
  return `${url}${sep}${noteTParam(seconds)}`;
}

/**
 * Extracts a note's stored text as plain text. Notes are saved as plain
 * text (AI-cleaned transcript line or the exact selected words) — the
 * bilingual spans you see in the notes list are added at render time and
 * never written back, so there is nothing to split here.
 */
function noteToParts(text) {
  return { original: stripHtmlToText(text) };
}

/**
 * Builds one Markdown note per video and writes it into the local Obsidian
 * vault via the native host (vault path is resolved host-side). Falls back
 * to a browser download when the host is missing or no "YouTube" vault exists.
 */
async function exportObsidianMd() {
  const btn = document.getElementById("exportObsidianBtn");
  const flash = (text) => {
    if (!btn) return;
    const original = btn.textContent;
    btn.textContent = text;
    setTimeout(() => {
      btn.textContent = original;
    }, 2000);
  };

  // In "All Notes" mode currentNotes spans several videos — narrow it down.
  const videoId = currentNotesFilterVideoId || currentVideoId;
  if (!videoId) {
    flash("Open a video first");
    return;
  }

  const notes = (currentNotes || [])
    .filter((note) => note.videoId === videoId)
    .sort(
      (a, b) =>
        (Number(a.timestampSeconds) || 0) - (Number(b.timestampSeconds) || 0),
    );

  if (notes.length === 0) {
    flash("No notes yet");
    return;
  }

  const url =
    currentVideoUrl || `https://www.youtube.com/watch?v=${videoId}`;
  const title = currentVideoTitle || videoId;
  const lines = [];

  // --- frontmatter ---
  lines.push("---");
  lines.push(`title: ${title}`);
  lines.push(`channel: ${currentChannelName || ""}`);
  lines.push(`videoId: ${videoId}`);
  lines.push(`url: ${url}`);
  if (currentVideoDuration) lines.push(`duration: ${currentVideoDuration}`);
  lines.push(`exported: ${new Date().toISOString().slice(0, 10)}`);
  lines.push("---");
  lines.push("");
  lines.push(`# ${title}`);
  lines.push("");

  // --- Overview chapters + key quotes (only when analysis is cached) ---
  if (currentAnalysis && Array.isArray(currentAnalysis.chapters)) {
    lines.push("## Chapters");
    lines.push("");
    currentAnalysis.chapters.forEach((ch) => {
      lines.push(
        `- **[${ch.timestamp}](${noteWithTs(url, ch.timestampSeconds)}) ${ch.title}** — ${ch.summary || ""}`,
      );
    });
    lines.push("");
    const quotes = currentAnalysis.keyQuotes || [];
    if (quotes.length > 0) {
      lines.push("## Key quotes");
      lines.push("");
      quotes.forEach((q) => {
        lines.push(
          `> [${q.timestamp}](${noteWithTs(url, q.timestampSeconds)}) ${q.quote}`,
        );
        lines.push("");
      });
    }
  }

  // --- manual timestamped notes ---
  lines.push("## Notes");
  lines.push("");
  notes.forEach((note, index) => {
    const ts = Math.floor(Number(note.timestampSeconds) || 0);
    const parts = noteToParts(note.text);
    lines.push(
      `- [${noteClock(ts)}](${noteWithTs(url, ts)}) ${parts.original || "(empty)"}`,
    );
    // 双语：只从界面翻译缓存里取译文（双语/中文模式下渲染笔记时已翻译过），
    // 缓存里没有就跳过 —— 导出本身永不触发 AI 调用、不花额度
    const translated = getInterfaceTranslation(
      "notes",
      getNoteTranslationId(note, index),
      note.text || "",
    );
    if (translated && translated !== parts.original) {
      lines.push(`  - ${translated}`);
    }
  });
  lines.push("");

  // --- transcript, so vault-wide search can find every spoken word ---
  if (currentTranscriptTimestamped) {
    lines.push("## Transcript");
    lines.push("");
    lines.push("```text");
    lines.push(currentTranscriptTimestamped.trimEnd());
    lines.push("```");
  }

  const content = lines.join("\n");

  // 首选：通过 native host 直写 vault，vault 路径由 host 自动解析
  try {
    const res = await chrome.runtime.sendMessage({
      action: "saveObsidianNote",
      videoId,
      title,
      channel: currentChannelName,
      content,
    });
    if (res?.success) {
      flash("Saved to vault");
      return;
    }
    if (res && !res.notInstalled && res.error) {
      // vault 缺失等明确报错 —— 打到 console 方便排查，内容仍走兜底不丢
      console.error("[YouTube Digest Panel] Obsidian export:", res.error);
    }
  } catch (_error) {
    // host 不可用，落到浏览器下载
  }

  // 兜底：浏览器下载 .md，手动拖进 vault
  downloadTextFile(
    content,
    `${title} [${videoId}].md`,
    "text/markdown;charset=utf-8",
  );
  flash("Exported .md");
}

// ============================================================
// LOCAL DOWNLOAD (Native Messaging)
// ============================================================

/**
 * Shows the Download button only when the local host is actually installed —
 * otherwise the button would just fail for everyone else.
 */
async function refreshNativeHostButton() {
  const btn = document.getElementById("downloadVideoBtn");
  if (!btn) return;
  try {
    const res = await chrome.runtime.sendMessage({ action: "pingNativeHost" });
    btn.style.display = res?.available ? "" : "none";
  } catch (_error) {
    btn.style.display = "none";
  }
}

/** Sends the current video to the local download.sh via the native host. */
async function downloadVideoLocally() {
  const btn = document.getElementById("downloadVideoBtn");
  if (!btn || !currentVideoUrl) return;

  const original = btn.textContent;
  btn.disabled = true;
  btn.textContent = "Downloading…";

  try {
    const res = await chrome.runtime.sendMessage({
      action: "downloadVideo",
      url: currentVideoUrl,
    });
    if (res?.success) {
      btn.textContent = "Saved";
    } else {
      btn.textContent = res?.notInstalled ? "No host" : "Failed";
      if (res?.output) {
        console.error("[YouTube Digest Panel] Download output:", res.output);
      }
    }
  } catch (error) {
    console.error("[YouTube Digest Panel] Download error:", error);
    btn.textContent = "Failed";
  } finally {
    setTimeout(() => {
      btn.textContent = original;
      btn.disabled = false;
    }, 3000);
  }
}

/** Quotes a CSV cell, doubling any quotes inside it. */
function csvCell(value) {
  return `"${String(value || "").replace(/"/g, '""')}"`;
}

/** Notes are stored as HTML; clip titles need plain text. */
function stripHtmlToText(html) {
  const holder = document.createElement("div");
  holder.innerHTML = html || "";
  return (holder.textContent || "").replace(/\s+/g, " ").trim();
}

/**
 * Renders the notes list in the Notes tab.
 */
function renderNotes(notes, filteredVideoId) {
  const notesList = document.getElementById("notesList");
  const notesIntro = document.getElementById("notesIntro");

  if (!notesList) return;

  notesList.innerHTML = "";

  if (!notes || notes.length === 0) {
    notesIntro.style.display = "block";
    notesIntro.textContent = filteredVideoId
      ? "No notes for this video yet. Hover over the video and click Note to save."
      : "No notes saved yet. Hover over a video and click Note to save.";
    return;
  }

  notesIntro.style.display = "none";

  notes.forEach((note, index) => {
    const translationId = getNoteTranslationId(note, index);
    const noteEl = document.createElement("div");
    noteEl.className = "note-item";
    noteEl.innerHTML = `
      <div class="note-header">
        <span class="note-timestamp" data-url="${escapeHtml(note.timestampedUrl)}" data-seconds="${Number(note.timestampSeconds) || 0}">${escapeHtml(note.timestamp)}</span>
        ${!filteredVideoId ? `<span class="note-video-title">${escapeHtml(note.videoTitle)}</span>` : ""}
      </div>
      <div class="note-text">${renderLocalizedContent(note.text, "notes", translationId)}</div>
      <div class="note-actions">
        <button class="note-action-btn note-copy-text">Copy text</button>
        <button class="note-action-btn note-copy-link" data-url="${escapeHtml(note.timestampedUrl)}">Copy timestamp</button>
        <button class="note-action-btn note-play" data-seconds="${Number(note.timestampSeconds) || 0}">Play</button>
        <button class="note-delete" data-id="${escapeHtml(note.id)}" type="button" aria-label="Delete note" title="Delete note">
          <svg viewBox="0 0 24 24" aria-hidden="true">
            <path d="M3 6h18"></path>
            <path d="M8 6V4h8v2"></path>
            <path d="m19 6-1 14H6L5 6"></path>
            <path d="M10 11v5"></path>
            <path d="M14 11v5"></path>
          </svg>
        </button>
      </div>
    `;

    // Timestamp click - play from this point (in this tab or a new one)
    noteEl.querySelector(".note-timestamp").addEventListener("click", () => {
      playNote(note);
    });

    // Delete button
    noteEl
      .querySelector(".note-delete")
      .addEventListener("click", async (e) => {
        e.stopPropagation();
        await deleteNote(note.id);
        loadNotes(filteredVideoId);
      });

    // Copy text button — copies just the note's text
    noteEl
      .querySelector(".note-copy-text")
      .addEventListener("click", async () => {
        try {
          await navigator.clipboard.writeText(
            getLocalizedPlainText(note.text, "notes", translationId),
          );
          const btn = noteEl.querySelector(".note-copy-text");
          btn.textContent = "Copied";
          setTimeout(() => {
            btn.textContent = "Copy text";
          }, 2000);
        } catch (err) {
          console.error("Copy failed:", err);
        }
      });

    // Copy timestamp button — copies the timestamped YouTube link
    noteEl
      .querySelector(".note-copy-link")
      .addEventListener("click", async () => {
        try {
          await navigator.clipboard.writeText(note.timestampedUrl);
          const btn = noteEl.querySelector(".note-copy-link");
          btn.textContent = "Copied";
          setTimeout(() => {
            btn.textContent = "Copy timestamp";
          }, 2000);
        } catch (err) {
          console.error("Copy failed:", err);
        }
      });

    // Play button (in this tab if it's the current video, else a new tab)
    noteEl.querySelector(".note-play").addEventListener("click", () => {
      playNote(note);
    });

    notesList.appendChild(noteEl);
  });

  if (currentTranscriptMode !== "original" && resultTabIsActive("notes")) {
    void translateNotesContent();
  }
}

/**
 * Deletes a note by ID.
 */
async function deleteNote(noteId) {
  try {
    await chrome.runtime.sendMessage({
      action: "deleteNote",
      noteId: noteId,
    });
  } catch (error) {
    console.error("[YouTube Digest Panel] Delete note error:", error);
  }
}

// ============================================================
// AUTO-SCROLL — Follow video playback in transcript
// ============================================================
// While a video plays, the transcript automatically scrolls to show which
// 30-second chunk is currently being spoken. If the user manually scrolls
// (e.g., to read ahead), auto-scroll pauses and a "Follow playback" button
// appears so they can resume it. Highlight always stays active regardless.

/**
 * Starts polling the video's current time and highlighting/scrolling
 * to the matching transcript entry.
 */
function startPlaybackTracking() {
  if (!currentTranscript || !currentTranscript.length) return;

  // Don't restart if already tracking (preserves user's auto-scroll state)
  if (autoScrollInterval) return;

  const willRestoreReadingPosition =
    pendingTranscriptViewState?.videoId === currentVideoId;
  autoScrollEnabled = !willRestoreReadingPosition;
  document.getElementById("followPlaybackBtn").style.display =
    willRestoreReadingPosition ? "block" : "none";

  // Poll video time every 500ms
  autoScrollInterval = setInterval(() => playbackTrackingTick(), 500);

  // Listen for manual scrolls on the content area
  const contentArea = document.getElementById("contentArea");
  contentArea.removeEventListener("scroll", onContentAreaScroll);
  contentArea.addEventListener("scroll", onContentAreaScroll);
}

/**
 * Stops playback tracking entirely. Called when leaving transcript tab,
 * starting a new digest, or leaving results state.
 */
function stopPlaybackTracking() {
  if (autoScrollInterval) {
    clearInterval(autoScrollInterval);
    autoScrollInterval = null;
  }
  autoScrollEnabled = true; // Reset for next time
  lastAutoScrollTime = 0;
  document.getElementById("followPlaybackBtn").style.display = "none";

  // Remove active highlights
  document
    .querySelectorAll(".transcript-entry.active-playback")
    .forEach((el) => {
      el.classList.remove("active-playback");
    });
}

/**
 * One tick of the playback tracker. Gets current video time from the
 * YouTube tab and highlights + scrolls to the matching transcript entry.
 */
async function playbackTrackingTick() {
  try {
    const result = await chrome.runtime.sendMessage({
      action: "relayToContent",
      payload: { action: "getCurrentTime" },
    });

    if (!result.success || !result.response) return;

    const currentTime = result.response.currentTime || 0;
    highlightActiveEntry(currentTime);
  } catch (error) {
    // Silently ignore — YouTube tab might be closed or navigated away
  }
}

/**
 * Scrolls the transcript to the entry currently being spoken (the one
 * carrying the active-playback highlight). Returns false if nothing is
 * highlighted yet. Stamps lastAutoScrollTime BEFORE scrolling so the scroll
 * events from our own smooth animation aren't mistaken for the user
 * scrolling away (which would re-disable auto-scroll immediately).
 */
function scrollToActiveEntry() {
  const activeEntry = document.querySelector(
    "#transcriptList .transcript-entry.active-playback",
  );
  if (!activeEntry) return false;

  lastAutoScrollTime = Date.now();
  activeEntry.scrollIntoView({ behavior: "smooth", block: "center" });
  return true;
}

/**
 * Finds the transcript entry matching the current playback time,
 * highlights it, and scrolls to it (if auto-scroll is enabled).
 *
 * @param {number} currentSeconds - Current video playback time in seconds
 */
function highlightActiveEntry(currentSeconds) {
  updateTimelinePlayhead(currentSeconds);
  const transcriptList = document.getElementById("transcriptList");
  if (!transcriptList) return;

  const entries = transcriptList.querySelectorAll(".transcript-entry");
  if (entries.length === 0) return;

  // Find the entry whose time range contains the current playback time
  let activeEntry = null;
  entries.forEach((entry, index) => {
    const entrySeconds = parseInt(entry.dataset.seconds);
    const nextEntry = entries[index + 1];
    const nextSeconds = nextEntry
      ? parseInt(nextEntry.dataset.seconds)
      : Infinity;

    if (currentSeconds >= entrySeconds && currentSeconds < nextSeconds) {
      activeEntry = entry;
    }
  });

  if (!activeEntry) return;

  // Skip if this entry is already highlighted (no DOM thrashing)
  if (activeEntry.classList.contains("active-playback")) return;

  // Remove old highlight, add new one
  entries.forEach((e) => e.classList.remove("active-playback"));
  activeEntry.classList.add("active-playback");

  // Only scroll if auto-scroll is enabled
  if (autoScrollEnabled) {
    lastAutoScrollTime = Date.now();
    activeEntry.scrollIntoView({ behavior: "smooth", block: "center" });
  }
}

/**
 * Scroll event handler for the content area.
 * Detects manual scrolling and disables auto-scroll so the user
 * can read at their own pace without being yanked back.
 */
function onContentAreaScroll() {
  scheduleTranscriptViewStateSave();

  // Ignore scroll events within 1 second of a programmatic scroll
  // (smooth scroll animations can last longer than a simple boolean flag)
  if (Date.now() - lastAutoScrollTime < 1000) return;

  // User scrolled manually — disable auto-scroll and show the button
  if (autoScrollEnabled && autoScrollInterval) {
    autoScrollEnabled = false;
    document.getElementById("followPlaybackBtn").style.display = "block";
  }
}

/**
 * Uses session storage when it is available. Local storage is a safe fallback
 * for older test or browser environments that do not expose session storage.
 */
function getTranscriptViewStateStorage() {
  return chrome.storage.session || chrome.storage.local;
}

/**
 * Reads one video's last visible transcript position.
 */
async function loadTranscriptViewState(videoId) {
  if (!videoId) return null;
  try {
    const result = await getTranscriptViewStateStorage().get(
      TRANSCRIPT_VIEW_STATE_KEY,
    );
    const state = result?.[TRANSCRIPT_VIEW_STATE_KEY]?.[videoId];
    const scrollTop = Number(state?.scrollTop);
    if (!Number.isFinite(scrollTop) || scrollTop < 0) return null;
    return { videoId, scrollTop };
  } catch (error) {
    console.error("[YouTube Digest] Reading position load error:", error);
    return null;
  }
}

/**
 * Stores positions for a small recent set of videos. This prevents one value
 * from growing without a limit during a long Chrome session.
 */
async function saveTranscriptViewState(videoId, scrollTop) {
  if (!videoId || !Number.isFinite(scrollTop) || scrollTop < 0) return;
  try {
    const storage = getTranscriptViewStateStorage();
    const result = await storage.get(TRANSCRIPT_VIEW_STATE_KEY);
    const states = result?.[TRANSCRIPT_VIEW_STATE_KEY] || {};
    states[videoId] = { scrollTop, updatedAt: Date.now() };

    const recentStates = Object.fromEntries(
      Object.entries(states)
        .sort(([, a], [, b]) => (b.updatedAt || 0) - (a.updatedAt || 0))
        .slice(0, 20),
    );
    await storage.set({ [TRANSCRIPT_VIEW_STATE_KEY]: recentStates });
  } catch (error) {
    console.error("[YouTube Digest] Reading position save error:", error);
  }
}

/**
 * Saves the visible position after scrolling stops. Capturing the video ID and
 * position now prevents a later video change from writing the wrong state.
 */
function scheduleTranscriptViewStateSave() {
  if (
    isRestoringTranscriptView ||
    !currentVideoId ||
    !transcriptTabIsActive()
  ) {
    return;
  }
  const contentArea = document.getElementById("contentArea");
  if (!contentArea) return;

  const videoId = currentVideoId;
  const scrollTop = contentArea.scrollTop;
  lastTranscriptScrollTop = scrollTop;
  clearTimeout(transcriptViewStateSaveTimer);
  transcriptViewStateSaveTimer = setTimeout(() => {
    void saveTranscriptViewState(videoId, scrollTop);
  }, 150);
}

/**
 * Saves immediately before the panel closes.
 */
function saveCurrentTranscriptViewState() {
  clearTimeout(transcriptViewStateSaveTimer);
  const contentArea = document.getElementById("contentArea");
  if (!currentVideoId || !contentArea) return Promise.resolve();
  if (transcriptTabIsActive()) captureCurrentTranscriptScrollTop();
  return saveTranscriptViewState(currentVideoId, lastTranscriptScrollTop);
}

/**
 * Returns true only while the Transcript tab is the visible results panel.
 */
function transcriptTabIsActive() {
  return resultTabIsActive("transcript");
}

function resultTabIsActive(tabName) {
  return Boolean(
    document.querySelector(
      `.tab-panel[data-panel="${CSS.escape(tabName)}"].active`,
    ),
  );
}

/**
 * Copies the shared scroll area's current value into transcript-only state.
 */
function captureCurrentTranscriptScrollTop() {
  const contentArea = document.getElementById("contentArea");
  if (contentArea) lastTranscriptScrollTop = contentArea.scrollTop;
}

/**
 * Restores the saved position after the transcript becomes visible. Follow
 * Playback stays paused, so the next timer tick cannot move the panel again.
 */
function restorePendingTranscriptViewState(videoId) {
  const state = pendingTranscriptViewState;
  pendingTranscriptViewState = null;
  const contentArea = document.getElementById("contentArea");
  if (!state || state.videoId !== videoId) {
    contentArea?.classList.remove("restoring-transcript-view");
    return;
  }

  requestAnimationFrame(() => {
    if (currentVideoId !== videoId || !contentArea) {
      contentArea?.classList.remove("restoring-transcript-view");
      return;
    }

    isRestoringTranscriptView = true;
    lastAutoScrollTime = Date.now();
    autoScrollEnabled = false;
    contentArea.scrollTop = state.scrollTop;
    lastTranscriptScrollTop = state.scrollTop;
    document.getElementById("followPlaybackBtn").style.display = "block";
    contentArea.classList.remove("restoring-transcript-view");
    requestAnimationFrame(() => {
      isRestoringTranscriptView = false;
    });
  });
}

// ============================================================
// UNIVERSAL DISPLAY LANGUAGE — Original / Chinese / aligned bilingual
// ============================================================

async function loadDisplayLanguageMode(videoId) {
  if (!videoId) {
    setTranscriptModeButtons("original");
    return "original";
  }
  try {
    const stored = await chrome.storage.local.get(DISPLAY_LANGUAGE_MODE_KEY);
    const mode = stored?.[DISPLAY_LANGUAGE_MODE_KEY]?.[videoId]?.mode;
    currentTranscriptMode = DISPLAY_LANGUAGE_MODES.has(mode)
      ? mode
      : "original";
  } catch (error) {
    currentTranscriptMode = "original";
  }
  setTranscriptModeButtons(currentTranscriptMode);
  return currentTranscriptMode;
}

async function saveDisplayLanguageMode(videoId, mode) {
  if (!videoId || !DISPLAY_LANGUAGE_MODES.has(mode)) return;
  const stored = await chrome.storage.local.get(DISPLAY_LANGUAGE_MODE_KEY);
  const modes = stored?.[DISPLAY_LANGUAGE_MODE_KEY] || {};
  modes[videoId] = { mode, updatedAt: Date.now() };
  const recentModes = Object.fromEntries(
    Object.entries(modes)
      .sort(([, a], [, b]) => (b.updatedAt || 0) - (a.updatedAt || 0))
      .slice(0, 50),
  );
  await chrome.storage.local.set({
    [DISPLAY_LANGUAGE_MODE_KEY]: recentModes,
  });
}

function getActiveTranscriptSegments() {
  return groupTranscriptEntries(currentTranscript || []);
}

function transcriptTranslationCacheKey(segment) {
  return `${currentVideoId}:zh:semantic:${segment.id}`;
}

function setTranscriptModeButtons(mode) {
  document.querySelectorAll(".transcript-mode-btn").forEach((button) => {
    const active = button.dataset.transcriptMode === mode;
    button.classList.toggle("active", active);
    button.setAttribute("aria-pressed", String(active));
  });
}

async function handleDisplayLanguageModeChange(mode) {
  if (!DISPLAY_LANGUAGE_MODES.has(mode)) return;
  if (mode === currentTranscriptMode) return;

  currentTranscriptMode = mode;
  await saveDisplayLanguageMode(currentVideoId, mode);
  if (mode !== "original") interfaceTranslationFailures.clear();
  translationGeneration += 1;
  translationWorkCount = 0;
  setTranslatingSpinner(false);
  if (transcriptScrollObserver) transcriptScrollObserver.disconnect();
  transcriptScrollObserver = null;
  setTranscriptModeButtons(mode);
  const activeTabName =
    document.querySelector(".tab.active")?.dataset.tab || "transcript";

  if (mode === "original") {
    renderTranscript();
    if (currentAnalysis) renderAnalysisResults(currentAnalysis);
    if (currentNotes.length) renderNotes(currentNotes, currentNotesFilterVideoId);
    return;
  }

  if (currentAnalysis) {
    renderAnalysisResults(currentAnalysis);
  }
  if (currentNotes.length) {
    renderNotes(currentNotes, currentNotesFilterVideoId);
  }
  if (activeTabName === "overview" && currentAnalysis) {
    await translateOverviewContent();
  } else if (activeTabName === "notes" && currentNotes.length) {
    await translateNotesContent();
  } else if (activeTabName === "transcript") {
    await translateTranscript();
  }
}

function renderTranscriptSegmentContent(segment, mode, translated, error) {
  const original = renderSubtitleInlineMarkup(segment.text);
  let translationHtml = "";
  if (translated) {
    translationHtml = renderSubtitleInlineMarkup(translated);
  } else if (error) {
    translationHtml = `${escapeHtml(error)}<button class="translation-retry-btn" type="button">Retry</button>`;
  } else {
    translationHtml = "Waiting for translation…";
  }

  if (mode === "bilingual") {
    return `<span class="transcript-copy"><span class="transcript-original">${original}</span><span class="transcript-translation ${translated ? "" : error ? "translation-error" : "translation-pending"}">${translationHtml}</span></span>`;
  }

  return `<span class="transcript-copy"><span class="transcript-translation ${translated ? "" : error ? "translation-error" : "translation-pending"}">${translationHtml}</span></span>`;
}

function renderTranscriptModeRows(segments, mode) {
  const transcriptList = document.getElementById("transcriptList");
  if (!transcriptList) return [];
  transcriptList.innerHTML = "";

  const existingBadge = document.getElementById("transcriptSourceBadge");
  if (existingBadge) existingBadge.remove();

  const rows = [];
  segments.forEach((segment, index) => {
    const div = document.createElement("div");
    const cached = transcriptParagraphCache.get(
      transcriptTranslationCacheKey(segment),
    );
    div.className = `transcript-entry ${cached ? "translated" : "translating"}`;
    div.dataset.seconds = segment.start;
    div.dataset.segmentId = segment.id;
    div.dataset.segmentIndex = index;

    const minutes = Math.floor(segment.start / 60);
    const seconds = Math.floor(segment.start % 60);
    const timestamp = `${minutes}:${String(seconds).padStart(2, "0")}`;
    div.innerHTML = `
      <span class="transcript-time">${timestamp}</span>
      ${renderTranscriptSegmentContent(segment, mode, cached, "")}
    `;
    div.addEventListener("click", (event) =>
      seekFromTranscriptEntryClick(event, segment.start),
    );
    transcriptList.appendChild(div);
    rows.push(div);
  });

  // Bilingual mode can find source text before each translation arrives.
  refreshTranscriptSearch({ preserveIndex: false, scroll: false });

  startPlaybackTracking();
  return rows;
}

/**
 * Rebuilds a provider response in source order. Unknown IDs are ignored and
 * missing IDs remain explicit errors, never positional guesses.
 */
function alignTranslatedSegmentBatch(sourceSegments, responseSegments) {
  const translatedById = new Map();
  if (Array.isArray(responseSegments)) {
    responseSegments.forEach((item) => {
      if (!item || typeof item.id !== "string" || typeof item.text !== "string")
        return;
      const text = item.text.trim();
      if (text && !translatedById.has(item.id)) {
        translatedById.set(item.id, text);
      }
    });
  }

  return sourceSegments.map((segment) => ({
    id: segment.id,
    text: translatedById.get(segment.id) || "",
    error: translatedById.has(segment.id) ? "" : "Translation unavailable.",
  }));
}

function updateTranslatedRow(segment, index, alignedItem, generation) {
  if (generation !== translationGeneration) return;
  const row = document.querySelector(
    `.transcript-entry[data-segment-id="${CSS.escape(segment.id)}"]`,
  );
  if (!row) return;

  if (alignedItem.text) {
    transcriptParagraphCache.set(
      transcriptTranslationCacheKey(segment),
      alignedItem.text,
    );
  }

  const copy = row.querySelector(".transcript-copy");
  if (copy) {
    copy.outerHTML = renderTranscriptSegmentContent(
      segment,
      currentTranscriptMode,
      alignedItem.text,
      alignedItem.error,
    );
  }
  row.classList.toggle("translated", !!alignedItem.text);
  row.classList.toggle("translating", false);
  row.classList.toggle("translation-failed", !alignedItem.text);

  const retry = row.querySelector(".translation-retry-btn");
  if (retry) {
    ["mousedown", "mouseup"].forEach((eventName) => {
      retry.addEventListener(eventName, (event) => {
        event.preventDefault();
        event.stopPropagation();
      });
    });
    retry.addEventListener("click", (event) => {
      event.preventDefault();
      event.stopPropagation();
      retryTranslationSegment(index, generation);
    });
  }
}

let activeTranslationQueue = null;

async function requestTranscriptTranslationBatch(
  indices,
  segments,
  generation,
  videoId,
  mode,
) {
  const sourceBatch = indices.map((index) => segments[index]);
  setTranslatingSpinner(true);
  try {
    const result = await sendTranslationMessage({
      action: "translateContent",
      content: {
        segments: sourceBatch.map(({ id, text }) => ({ id, text })),
      },
      contentType: "transcriptBatch",
      targetLanguage: "zh",
      videoTitle: currentVideoTitle,
    });

    const isStale =
      generation !== translationGeneration ||
      videoId !== currentVideoId ||
      mode !== currentTranscriptMode;
    if (isStale) return;

    const responseSegments = result?.success
      ? result.translatedContent?.segments
      : [];
    const aligned = alignTranslatedSegmentBatch(sourceBatch, responseSegments);
    aligned.forEach((item, batchIndex) => {
      if (!result?.success) {
        item.error = result?.error || "Translation failed.";
      }
      updateTranslatedRow(
        sourceBatch[batchIndex],
        indices[batchIndex],
        item,
        generation,
      );
    });
    refreshTranscriptSearch({ preserveIndex: true, scroll: false });
    await updateCache();
  } catch (error) {
    if (generation !== translationGeneration) return;
    sourceBatch.forEach((segment, batchIndex) => {
      updateTranslatedRow(
        segment,
        indices[batchIndex],
        { id: segment.id, text: "", error: error.message || "Translation failed." },
        generation,
      );
    });
    refreshTranscriptSearch({ preserveIndex: true, scroll: false });
  } finally {
    setTranslatingSpinner(false);
  }
}

function retryTranslationSegment(index, generation) {
  if (generation !== translationGeneration || !activeTranslationQueue) return;
  const row = document.querySelector(
    `.transcript-entry[data-segment-index="${index}"]`,
  );
  if (row) {
    row.classList.add("translating");
    row.classList.remove("translation-failed");
    const translation = row.querySelector(".transcript-translation");
    if (translation) {
      translation.className = "transcript-translation translation-pending";
      translation.textContent = "Retrying…";
    }
  }
  activeTranslationQueue.enqueue(index, true);
}

/**
 * Renders immediately, translates the first small batch, then observes the
 * remaining rows. Batches are sequential so the provider is never flooded.
 */
async function translateTranscript() {
  const segments = getActiveTranscriptSegments();
  if (!segments.length || currentTranscriptMode === "original") return;

  const generation = translationGeneration;
  const videoId = currentVideoId;
  const mode = currentTranscriptMode;
  if (transcriptScrollObserver) transcriptScrollObserver.disconnect();

  const rows = renderTranscriptModeRows(segments, mode);
  const queue = [];
  const queued = new Set();
  let processing = false;

  const processNext = async () => {
    if (processing || queue.length === 0 || generation !== translationGeneration)
      return;
    processing = true;
    const indices = queue.splice(0, TRANSLATION_BATCH_SIZE);
    indices.forEach((index) => queued.delete(index));
    try {
      await requestTranscriptTranslationBatch(
        indices,
        segments,
        generation,
        videoId,
        mode,
      );
    } finally {
      processing = false;
      if (queue.length && generation === translationGeneration) processNext();
    }
  };

  const enqueue = (index, force = false) => {
    if (!Number.isInteger(index) || !segments[index]) return;
    const cached = transcriptParagraphCache.has(
      transcriptTranslationCacheKey(segments[index]),
    );
    if ((!force && cached) || queued.has(index)) return;
    queue.push(index);
    queued.add(index);
    // Let all entries reported in the same viewport turn collect before the
    // worker starts, producing one small contextual multi-segment request.
    Promise.resolve().then(processNext);
  };
  activeTranslationQueue = { enqueue };

  transcriptScrollObserver = new IntersectionObserver(
    (observerEntries) => {
      observerEntries
        .filter((entry) => entry.isIntersecting)
        .sort(
          (a, b) =>
            Number(a.target.dataset.segmentIndex) -
            Number(b.target.dataset.segmentIndex),
        )
        .forEach((entry) => enqueue(Number(entry.target.dataset.segmentIndex)));
    },
    {
      root: document.getElementById("contentArea"),
      rootMargin: "320px 0px",
      threshold: 0,
    },
  );

  rows.forEach((row, index) => {
    if (!row.classList.contains("translated")) transcriptScrollObserver.observe(row);
    if (index < TRANSLATION_BATCH_SIZE) enqueue(index);
  });
}

function setTranslatingSpinner(show) {
  if (show) translationWorkCount += 1;
  else translationWorkCount = Math.max(0, translationWorkCount - 1);
  const isTranslating = translationWorkCount > 0;
  const spinner = document.getElementById("langSpinner");
  if (spinner) spinner.classList.toggle("visible", isTranslating);
}

// Pure helpers are exposed for the repository's Node tests. The extension does
// not read this object at runtime.
globalThis.__YTD_TRANSCRIPT_TESTING__ = {
  sendTranslationMessage,
  groupTranscriptEntries,
  splitOversizedThought,
  alignTranslatedSegmentBatch,
  findLiteralTranscriptMatches,
  loadTranscriptViewState,
  saveTranscriptViewState,
  loadDisplayLanguageMode,
  saveDisplayLanguageMode,
  getNavigationUrl,
  renderSubtitleInlineMarkup,
  renderTranscriptSegmentContent,
};
