package main

import (
	"archive/zip"
	"bufio"
	"bytes"
	"crypto/sha256"
	"crypto/tls"
	"encoding/json"
	"fmt"
	"io"
	"net"
	"net/http"
	"os"
	"os/exec"
	"os/signal"
	"path/filepath"
	"regexp"
	"runtime"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"
	"unicode/utf8"
)

const (
	ScriptVersion = "1.4.4"
	LogFileName   = "farming_log.txt"

	DeltaDownloadURL    = "https://delta.filenetwork.vip/android.html"
	DeltaAPIURL         = "https://delta.filenetwork.vip/get_files.php"
	DiscordInviteURL    = "discord.gg/6jg6PbWrz"

	// ========================================================================
	// CENTRALIZED TERMINAL UI & DASHBOARD CONFIGURATION
	// ========================================================================
	DASHBOARD_MAX_WIDTH         = 76
	DASHBOARD_MIN_WIDTH         = 40
	TERMINAL_SAFETY_MARGIN      = 2
	CENTER_DASHBOARD            = true
	CENTER_DASHBOARD_VERTICALLY = false
	WRAP_LONG_VALUES            = true
	SHORTEN_LONG_VALUES         = true
)

var VersionURL = func() string {
	repo := os.Getenv("NEF_REPO")
	if repo == "" {
		repo = "relayced/test-nef"
	}
	return fmt.Sprintf("https://raw.githubusercontent.com/%s/main/version.txt", repo)
}()

// ANSI Color Palette
const (
	NC    = "\033[0m"
	Bold  = "\033[1m"
	Dim   = "\033[2m"
	White = "\033[1;37m"
	Gray  = "\033[38;5;244m"
	Dark  = "\033[38;5;238m"
	Cyan  = "\033[38;5;75m"
	Green = "\033[38;5;78m"
	Amber = "\033[38;5;214m"
	Red   = "\033[38;5;203m"
)

var allPackages = []string{
	"com.roblox.clienb",
	"com.roblox.clienc",
	"com.roblox.cliend",
	"com.roblox.cliene",
	"com.roblox.clienf",
	"com.roblox.clieng",
}

// CleanMode defines the depth of pre-launch system optimization.
type CleanMode int

const (
	CleanModeDeep CleanMode = iota // Kill safe background apps + flush caches + compact RAM
	CleanModeLight                 // Purge stale clones + flush caches only
	CleanModeNone                  // Skip
)

var (
	cleanMode         = CleanModeDeep
	cleanedRAMFreedMB int
	cleanedAppsCount  int
	cleanedModeDesc   = "Deep Clean"
)

var protectedPackagePrefixes = []string{
	"com.termux",
	"com.topjohnwu.magisk",
	"io.github.a13e300.ksu",
	"me.weishu.kernelsu",
	"io.github.vvb2060.magisk",
	"org.lsposed.manager",
	"android",
	"com.android.systemui",
	"com.android.phone",
	"com.android.server.telecom",
	"com.google.android.gms",
	"com.google.android.gsf",
	"com.google.android.vending",
	"com.google.android.inputmethod.latin",
	"com.touchtype.swiftkey",
	"com.samsung.android.honeyboard",
	"com.android.inputmethod.latin",
}

var commonHeavyPackages = []string{
	"com.android.chrome",
	"com.google.android.youtube",
	"com.google.android.apps.youtube.music",
	"com.zhiliaoapp.musically",
	"com.ss.android.ugc.trill",
	"com.facebook.katana",
	"com.facebook.orca",
	"com.instagram.android",
	"com.twitter.android",
	"tv.twitch.android",
	"com.netflix.mediaclient",
	"com.spotify.music",
	"org.mozilla.firefox",
	"com.microsoft.emmx",
	"com.opera.browser",
	"com.brave.browser",
	"com.sec.android.app.sbrowser",
	"com.snapchat.android",
	"com.reddit.frontpage",
	"com.discord",
}

func isProtectedPackage(pkg string) bool {
	for _, prefix := range protectedPackagePrefixes {
		if strings.HasPrefix(pkg, prefix) {
			return true
		}
	}
	return false
}

// Global runtime configurations
var (
	licenseKey      = "Free"
	licenseDuration = "Free"
	isUniversalKey  bool
	myHWID          string
	discordWebhook  string
	discordMention  string
	gameName        string
	gameURL         string
	cloneCount      int
	enableRejoin    bool
	activePackages  []string

	serverPlaceID  string
	serverGameName string

	// Per-clone game assignment — populated by configureTargetExperience.
	// Index i corresponds to activePackages[i]. Replaces global gameURL/gameName
	// at all launch and recovery call sites when Mixed mode is active.
	cloneGameConfigs []CloneGameConfig

	inputChan = make(chan string, 16)

	consoleMu     sync.Mutex
	activeSpinner *spinnerState

	logMu sync.Mutex

	globalRecoveryLock sync.Mutex
	recoveringClones   = make(map[string]bool)
	recoveringMu       sync.Mutex

	cloneRecoveryCooldown   = make(map[string]time.Time)
	cloneRecoveryCooldownMu sync.Mutex

	networkMu     sync.RWMutex
	networkOnline = true

	playerPkgMap        = make(map[string]string)
	playerPkgMu         sync.RWMutex
	recentlyLaunchedPkg string
	recentlyLaunchedMu  sync.Mutex
)

// CloneGameConfig holds the Roblox deep-link URL and display name for a single clone.
type CloneGameConfig struct {
	URL  string
	Name string
}

// getCloneGameConfig returns the game config assigned to a package.
// Falls back to the global gameName/gameURL for backward compatibility when
// cloneGameConfigs has not been populated (single-game mode).
func getCloneGameConfig(pkg string) CloneGameConfig {
	for i, p := range activePackages {
		if p == pkg && i < len(cloneGameConfigs) {
			return cloneGameConfigs[i]
		}
	}
	return CloneGameConfig{URL: gameURL, Name: gameName}
}

// State helpers to prevent spam reopening and duplicate crash/disconnect triggers
func isCloneRecoveringOrCooldown(pkg string) bool {
	recoveringMu.Lock()
	if recoveringClones[pkg] {
		recoveringMu.Unlock()
		return true
	}
	recoveringMu.Unlock()

	cloneRecoveryCooldownMu.Lock()
	defer cloneRecoveryCooldownMu.Unlock()
	if expireTime, exists := cloneRecoveryCooldown[pkg]; exists {
		if time.Now().Before(expireTime) {
			return true
		}
		delete(cloneRecoveryCooldown, pkg)
	}
	return false
}

func setCloneRecoveryCooldown(pkg string, d time.Duration) {
	cloneRecoveryCooldownMu.Lock()
	cloneRecoveryCooldown[pkg] = time.Now().Add(d)
	cloneRecoveryCooldownMu.Unlock()
}

// Health and Stagnant RAM watchdog tracking
type cloneHealthInfo struct {
	lastRAM        int
	stagnantCycles int
	lastPID        int
	zeroCycles     int
	launchedAt     time.Time
}

var (
	cloneHealthStore = make(map[string]*cloneHealthInfo)
	cloneHealthMu    sync.Mutex
)

func markCloneLaunched(pkg string) {
	cloneHealthMu.Lock()
	cloneHealthStore[pkg] = &cloneHealthInfo{
		launchedAt: time.Now(),
	}
	cloneHealthMu.Unlock()
}

// hideSoftKeyboard dismisses the Android soft keyboard via the input_method system service.
// This uses a pure service-level call (no keyevent dispatched) so it cannot trigger
// Roblox's in-game escape/leave modal or any other app-level key handler.
func hideSoftKeyboard() {
	// 'cmd input_method hide_soft_input' talks directly to InputMethodManagerService
	// and hides the IME without sending KEYCODE_BACK or KEYCODE_ESCAPE to any window.
	_ = exec.Command("cmd", "input_method", "hide_soft_input").Run()
}

// isProcessAlive checks whether the process PID exists in kernel procfs and is not a zombie.
func isProcessAlive(pid int) bool {
	if pid <= 0 {
		return false
	}
	statPath := fmt.Sprintf("/proc/%d/stat", pid)
	data, err := os.ReadFile(statPath)
	if err != nil && checkRoot() {
		out, rErr := exec.Command("su", "-c", "cat "+statPath).Output()
		if rErr == nil {
			data = out
			err = nil
		}
	}
	if err != nil || len(data) == 0 {
		return false
	}
	fields := strings.Fields(string(data))
	if len(fields) >= 3 {
		state := fields[2]
		if state == "Z" { // Zombie process
			return false
		}
	}
	return true
}



// ============================================================================
// ANIMATED SPINNER & THREAD-SAFE CONSOLE SUBSYSTEM
// ============================================================================

var spinnerFrames = []string{"⠋", "⠙", "⠹", "⠸", "⠼", "⠴", "⠦", "⠧", "⠇", "⠏"}

var renderMu sync.Mutex

type launchCardStateInfo struct {
	sync.Mutex
	Active      bool
	ActiveClone int
	TotalClones int
	Phase       string
	Detail      string
}

var currentLaunchCard launchCardStateInfo

type spinnerState struct {
	label     string
	remaining int // seconds remaining, or -1 if indefinite
	total     int
	frameIdx  int
	done      bool
}

func (s *spinnerState) renderUnsafe() {
	if s.done {
		return
	}
	dashboardMu.Lock()
	monitoring := isMonitoringActive
	dashboardMu.Unlock()
	currentLaunchCard.Lock()
	launchActive := currentLaunchCard.Active
	currentLaunchCard.Unlock()
	if monitoring || launchActive {
		return
	}
	pad := getMenuLeftPad()
	frame := spinnerFrames[s.frameIdx%len(spinnerFrames)]
	if s.remaining >= 0 {
		fmt.Printf("\r\033[K%s  %s%s%s %-36s %s[%2ds]%s", pad, Cyan, frame, NC, s.label, White, s.remaining, NC)
	} else {
		fmt.Printf("\r\033[K%s  %s%s%s %s", pad, Cyan, frame, NC, s.label)
	}
}

// safeLog cleanly logs a message, erasing any active spinner frame, printing the log with centered padding,
// and redrawing the active spinner beneath it. This prevents any log interleaving or collisions.
func safeLog(format string, a ...interface{}) {
	consoleMu.Lock()
	defer consoleMu.Unlock()

	if activeSpinner != nil && !activeSpinner.done {
		fmt.Print("\r\033[K")
	}

	dashboardMu.Lock()
	active := isMonitoringActive
	dashboardMu.Unlock()

	if active {
		msg := fmt.Sprintf(format, a...)
		writeLog("SENTINEL", msg)
		return
	}

	pad := getMenuLeftPad()
	rawMsg := fmt.Sprintf(format, a...)
	lines := strings.Split(rawMsg, "\n")
	var sb strings.Builder
	for i, line := range lines {
		if i == len(lines)-1 && line == "" {
			continue
		}
		if line != "" {
			sb.WriteString(pad)
			sb.WriteString(line)
		}
		sb.WriteString("\n")
	}
	fmt.Print(sb.String())

	if activeSpinner != nil && !activeSpinner.done {
		activeSpinner.renderUnsafe()
	}
}

// runAnimatedCountdown runs a synchronized countdown with a smooth braille spinner.
// When a 24/7 monitoring dashboard or launch card is active, it renders cleanly INSIDE the
// card rows so cooldowns, engine initializations, and live RAM telemetry never clash or tear.
func runAnimatedCountdown(label string, totalSeconds int, doneTag string, doneMsg string) {
	if totalSeconds <= 0 {
		return
	}

	dashboardMu.Lock()
	monitoring := isMonitoringActive
	dashboardMu.Unlock()

	currentLaunchCard.Lock()
	launchActive := currentLaunchCard.Active
	launchClone := currentLaunchCard.ActiveClone
	launchTotal := currentLaunchCard.TotalClones
	launchPhase := currentLaunchCard.Phase
	currentLaunchCard.Unlock()

	cleanLabel := strings.TrimSpace(strings.TrimSuffix(strings.TrimSpace(label), "..."))
	actionCol := Cyan
	lowerLabel := strings.ToLower(cleanLabel)
	if strings.Contains(lowerLabel, "cool") || strings.Contains(lowerLabel, "stabiliz") {
		actionCol = Amber
	}

	// 1. In-Dashboard 24/7 Sentinel Watchdog Mode
	if monitoring {
		for rem := totalSeconds; rem > 0; rem-- {
			frame := spinnerFrames[(totalSeconds-rem)%len(spinnerFrames)]
			dashboardMu.Lock()
			currentDashboard.ActionStep = fmt.Sprintf("%s %s [%2ds]", frame, cleanLabel, rem)
			currentDashboard.ActionColor = actionCol
			dashboardMu.Unlock()

			drawSummaryCard()
			time.Sleep(1 * time.Second)
		}

		dashboardMu.Lock()
		currentDashboard.ActionStep = ""
		dashboardMu.Unlock()
		drawSummaryCard()

		if doneTag != "" && doneMsg != "" {
			writeLog(doneTag, doneMsg)
		}
		return
	}

	// 2. In-Launch-Card Pre-Flight Mode
	if launchActive {
		for rem := totalSeconds; rem > 0; rem-- {
			frame := spinnerFrames[(totalSeconds-rem)%len(spinnerFrames)]
			detailText := fmt.Sprintf("%s %s [%2ds]", frame, cleanLabel, rem)
			drawLaunchStatusCard(launchClone, launchTotal, launchPhase, detailText)
			time.Sleep(1 * time.Second)
		}
		if doneMsg != "" {
			drawLaunchStatusCard(launchClone, launchTotal, launchPhase, doneMsg)
		}
		if doneTag != "" && doneMsg != "" {
			writeLog(doneTag, doneMsg)
		}
		return
	}

	// 3. Fallback Raw Console Mode (Initial Menus / Key Check)
	s := &spinnerState{
		label:     label,
		remaining: totalSeconds,
		total:     totalSeconds,
	}

	consoleMu.Lock()
	activeSpinner = s
	s.renderUnsafe()
	consoleMu.Unlock()

	frameTicker := time.NewTicker(80 * time.Millisecond)
	defer frameTicker.Stop()
	secondTicker := time.NewTicker(1 * time.Second)
	defer secondTicker.Stop()

	for s.remaining > 0 {
		select {
		case <-frameTicker.C:
			consoleMu.Lock()
			if activeSpinner == s && !s.done {
				s.frameIdx++
				s.renderUnsafe()
			}
			consoleMu.Unlock()

		case <-secondTicker.C:
			consoleMu.Lock()
			if activeSpinner == s && !s.done {
				s.remaining--
				if s.remaining >= 0 {
					s.renderUnsafe()
				}
			}
			consoleMu.Unlock()
		}
	}

	consoleMu.Lock()
	s.done = true
	if activeSpinner == s {
		activeSpinner = nil
	}
	fmt.Print("\r\033[K")
	currTime := time.Now().Format("15:04:05")
	if doneTag != "" && doneMsg != "" {
		fmt.Printf("[%s] %s[%s]%s   %s\n", currTime, Green, doneTag, NC, doneMsg)
		writeLog(doneTag, doneMsg)
	}
	consoleMu.Unlock()
}

// runAnimatedTask displays a spinner while an asynchronous task executes.
func runAnimatedTask(label string, task func() error) error {
	s := &spinnerState{
		label:     label,
		remaining: -1,
	}

	consoleMu.Lock()
	activeSpinner = s
	s.renderUnsafe()
	consoleMu.Unlock()

	ticker := time.NewTicker(80 * time.Millisecond)
	defer ticker.Stop()

	doneChan := make(chan error, 1)
	go func() {
		doneChan <- task()
	}()

	for {
		select {
		case <-ticker.C:
			consoleMu.Lock()
			if activeSpinner == s && !s.done {
				s.frameIdx++
				s.renderUnsafe()
			}
			consoleMu.Unlock()

		case err := <-doneChan:
			consoleMu.Lock()
			s.done = true
			if activeSpinner == s {
				activeSpinner = nil
			}
			fmt.Print("\r\033[K")
			consoleMu.Unlock()
			return err
		}
	}
}

// ============================================================================
// HELPER UTILITIES
// ============================================================================

func getCloneDisplayName(pkg string) string {
	for i, p := range allPackages {
		if p == pkg {
			return fmt.Sprintf("Clone %d", i+1)
		}
	}
	if strings.Contains(pkg, "Clone") {
		return pkg
	}
	return "Clone 1"
}

func cleanSentinelLogLine(line string) string {
	ansiRegex := regexp.MustCompile(`\x1b\[[0-9;]*[a-zA-Z]`)
	cleaned := ansiRegex.ReplaceAllString(line, "")
	cleaned = strings.ReplaceAll(cleaned, "@everyone", "@\u200beveryone")
	cleaned = strings.ReplaceAll(cleaned, "@here", "@\u200bhere")
	return strings.TrimSpace(cleaned)
}

func plural(n int) string {
	if n == 1 {
		return ""
	}
	return "s"
}

// ============================================================================
// RESOURCE METRICS & MONITORING SUBSYSTEM
// ============================================================================

type SystemResourceStats struct {
	TotalRAMMB      int
	UsedRAMMB       int
	AvailableRAMMB  int
	RAMUsagePercent float64
	TotalRAMGB      float64
	UsedRAMGB       float64
	AvailableRAMGB  float64
	CPUUsagePercent float64
	CPUCores        int
	Bitness         int
	BitnessDesc     string
}

func getSystemBitness() (int, string) {
	bits := 32 << (^uint(0) >> 63)
	arch := runtime.GOARCH
	switch arch {
	case "arm64":
		return 64, "64-bit (ARM64)"
	case "arm":
		return 32, "32-bit (ARM)"
	case "amd64":
		return 64, "64-bit (x86_64)"
	default:
		if bits == 64 {
			return 64, fmt.Sprintf("64-bit (%s)", arch)
		}
		return 32, fmt.Sprintf("32-bit (%s)", arch)
	}
}

func getSystemCPUCores() int {
	// Respect container/cgroup allocation & CPU affinity (e.g. Redfinger Cloud Phone tier limits)
	// runtime.NumCPU() returns the actual number of logical CPUs allocated to this process/container
	if n := runtime.NumCPU(); n > 0 {
		return n
	}
	return 4
}

// getSystemResources collects kernel-level RAM from /proc/meminfo and CPU from /proc/stat.
func getSystemResources() SystemResourceStats {
	bits, bitDesc := getSystemBitness()
	stats := SystemResourceStats{
		CPUCores:    getSystemCPUCores(),
		Bitness:     bits,
		BitnessDesc: bitDesc,
	}

	// 1. Read /proc/meminfo
	data, err := os.ReadFile("/proc/meminfo")
	if err == nil {
		var totalKB, availKB, freeKB, buffersKB, cachedKB int
		for _, line := range strings.Split(string(data), "\n") {
			fields := strings.Fields(line)
			if len(fields) >= 2 {
				key := strings.TrimSuffix(fields[0], ":")
				val, _ := strconv.Atoi(fields[1])
				switch key {
				case "MemTotal":
					totalKB = val
				case "MemAvailable":
					availKB = val
				case "MemFree":
					freeKB = val
				case "Buffers":
					buffersKB = val
				case "Cached":
					cachedKB = val
				}
			}
		}

		if availKB == 0 {
			availKB = freeKB + buffersKB + cachedKB
		}
		if availKB > totalKB {
			availKB = totalKB
		}

		totalMB := totalKB / 1024
		availMB := availKB / 1024
		usedMB := totalMB - availMB
		if usedMB < 0 {
			usedMB = 0
		}

		stats.TotalRAMMB = totalMB
		stats.AvailableRAMMB = availMB
		stats.UsedRAMMB = usedMB
		stats.TotalRAMGB = float64(totalMB) / 1024.0
		stats.AvailableRAMGB = float64(availMB) / 1024.0
		stats.UsedRAMGB = float64(usedMB) / 1024.0

		if totalMB > 0 {
			stats.RAMUsagePercent = (float64(usedMB) / float64(totalMB)) * 100.0
		}
	}

	// 2. Read CPU from /proc/stat (two samples over 90ms)
	stats.CPUUsagePercent = getSystemCPUUsage()

	return stats
}

func getSystemCPUUsage() float64 {
	readStat := func() (idle, total uint64, err error) {
		data, err := os.ReadFile("/proc/stat")
		if err != nil {
			return 0, 0, err
		}
		for _, line := range strings.Split(string(data), "\n") {
			if strings.HasPrefix(line, "cpu ") {
				fields := strings.Fields(line)[1:]
				var sum uint64
				for i, f := range fields {
					val, _ := strconv.ParseUint(f, 10, 64)
					sum += val
					if i == 3 || i == 4 { // idle or iowait
						idle += val
					}
				}
				return idle, sum, nil
			}
		}
		return 0, 0, fmt.Errorf("no cpu line")
	}

	idle1, total1, err1 := readStat()
	if err1 != nil {
		return 0.0
	}
	time.Sleep(90 * time.Millisecond)
	idle2, total2, err2 := readStat()
	if err2 != nil || total2 <= total1 {
		return 0.0
	}

	deltaTotal := float64(total2 - total1)
	deltaIdle := float64(idle2 - idle1)
	usage := (1.0 - (deltaIdle / deltaTotal)) * 100.0
	if usage < 0 {
		usage = 0
	} else if usage > 100 {
		usage = 100
	}
	return usage
}

// Backward compatible helper for existing memory checks
func getSystemMemory() SystemResourceStats {
	return getSystemResources()
}

// RAM & CPU Balanced Clone Recommendation Formula:
// Base OS footprint requires ~1.5 - 2.2 GB RAM and 1-2 CPU cores for UI/kernel stability.
// Each Roblox Android clone consumes ~600 - 850 MB RSS and demands ~1.5 CPU cores of active workload.
// Quad-core (<= 4 cores) mobile devices are strictly capped at 2 clones to prevent 100% CPU lockups.
func getRecommendedClones(res SystemResourceStats) int {
	if res.TotalRAMMB == 0 {
		return 2 // default fallback
	}

	// 1. RAM Capacity Recommendation
	ramRec := 2
	total := res.TotalRAMMB
	if total < 2800 { // Under 3GB (e.g. 2GB device)
		ramRec = 1
	} else if total < 4600 { // ~3GB - 4GB RAM
		ramRec = 2
	} else if total < 6800 { // ~5GB - 6GB RAM
		ramRec = 3
	} else if total < 9000 { // ~7GB - 8GB RAM
		ramRec = 4
	} else if total < 13000 { // ~10GB - 12GB RAM
		ramRec = 5
	} else {
		ramRec = 6
	}

	// 2. CPU Core Capacity Recommendation
	// 4 cores or fewer: 2 clones maximum. Android OS + Termux take 2 cores; 2 clones take 2 cores.
	// 6 cores: 3 clones maximum.
	// 8 cores: 4 clones maximum (5 if 12GB+ RAM).
	cpuRec := 2
	cores := res.CPUCores
	if cores <= 2 {
		cpuRec = 1
	} else if cores <= 4 {
		cpuRec = 2
	} else if cores <= 6 {
		cpuRec = 3
	} else {
		cpuRec = 4
		if total >= 12000 && cores >= 8 {
			cpuRec = 5
		}
	}

	// If background CPU load is already heavy (> 45%), lower CPU allowance by 1
	if res.CPUUsagePercent > 45.0 && cpuRec > 1 {
		cpuRec--
	}

	// Balanced Recommendation: capped by the most constrained resource (RAM vs CPU)
	rec := ramRec
	if cpuRec < rec {
		rec = cpuRec
	}
	if rec < 1 {
		rec = 1
	}
	return rec
}

// ============================================================================
// GAME MEMORY PROFILES & PER-CLONE TRACKING
// ============================================================================

type GameMemoryProfile struct {
	Name            string
	EstimatedRAMMB  int
	ProfileCategory string
}

var knownGameProfiles = []GameMemoryProfile{
	{Name: "Steal An Egg", EstimatedRAMMB: 1450, ProfileCategory: "Heavy (Dynamic Assets & Physics)"},
	{Name: "Blox Fruits", EstimatedRAMMB: 1250, ProfileCategory: "Heavy (High Asset/Shaders)"},
	{Name: "Pet Simulator 99", EstimatedRAMMB: 1150, ProfileCategory: "Heavy (High Entity Count)"},
	{Name: "Blade Ball", EstimatedRAMMB: 850, ProfileCategory: "Moderate (Fast Arena Action)"},
	{Name: "Fisch", EstimatedRAMMB: 980, ProfileCategory: "Moderate-Heavy (Water Shaders)"},
	{Name: "Anime Defenders", EstimatedRAMMB: 1050, ProfileCategory: "Heavy (Tower Defense Units)"},
	{Name: "Generic Roblox", EstimatedRAMMB: 950, ProfileCategory: "Standard Roblox Mobile Baseline"},
}

func getGameProfile(name string) GameMemoryProfile {
	lowName := strings.ToLower(name)
	for _, p := range knownGameProfiles {
		if strings.Contains(lowName, strings.ToLower(p.Name)) {
			return p
		}
	}
	return knownGameProfiles[len(knownGameProfiles)-1]
}

type CloneResourceReport struct {
	DisplayName string
	Package     string
	PID         int
	RAMMB       int
	IsEstimated bool
	GameProfile string
	Status      string
}

// CloneTelemetrySnapshot caches live measured process memory so crashes and freezes
// retain their actual recorded memory rather than falling back to generic estimates.
type CloneTelemetrySnapshot struct {
	PID         int
	RAMMB       int
	IsEstimated bool
	Timestamp   time.Time
}

type cloneTelemetryStore struct {
	mu   sync.RWMutex
	data map[string]CloneTelemetrySnapshot
}

var telemetryStore = &cloneTelemetryStore{
	data: make(map[string]CloneTelemetrySnapshot),
}

func (s *cloneTelemetryStore) Set(pkg string, pid, ramMB int) {
	if ramMB <= 0 {
		return
	}
	s.mu.Lock()
	s.data[pkg] = CloneTelemetrySnapshot{
		PID:         pid,
		RAMMB:       ramMB,
		IsEstimated: false,
		Timestamp:   time.Now(),
	}
	s.mu.Unlock()
}

func (s *cloneTelemetryStore) Get(pkg string) (CloneTelemetrySnapshot, bool) {
	s.mu.RLock()
	defer s.mu.RUnlock()
	val, ok := s.data[pkg]
	return val, ok
}

// checkRoot tests if su is available to bypass Android 10 SELinux UID sandboxing.
var (
	isRooted      bool
	rootCheckDone bool
	rootMu        sync.Mutex
)

func checkRoot() bool {
	rootMu.Lock()
	defer rootMu.Unlock()
	if rootCheckDone {
		return isRooted
	}
	rootCheckDone = true
	out, err := exec.Command("su", "-c", "id").CombinedOutput()
	if err == nil && (strings.Contains(string(out), "uid=0") || strings.Contains(string(out), "root")) {
		isRooted = true
	}
	return isRooted
}

func parseDumpsysMeminfo(output string) (int, int, bool) {
	var pid int
	var ramMB int

	// Extract PID: ** MEMINFO in pid 18452 [com.roblox.client] **
	rePID := regexp.MustCompile(`(?i)(?:\*\* MEMINFO in pid|pid)\s+([0-9]+)`)
	if m := rePID.FindStringSubmatch(output); len(m) > 1 {
		if p, err := strconv.Atoi(m[1]); err == nil && p > 0 {
			pid = p
		}
	}

	// Extract Memory: prefer TOTAL RSS, then TOTAL PSS, then TOTAL:, then table row
	reRSS := regexp.MustCompile(`(?i)TOTAL\s+RSS:\s*([0-9]+)`)
	if m := reRSS.FindStringSubmatch(output); len(m) > 1 {
		if kb, err := strconv.Atoi(m[1]); err == nil && kb > 0 {
			ramMB = kb / 1024
			return pid, ramMB, true
		}
	}

	rePSS := regexp.MustCompile(`(?i)TOTAL\s+PSS:\s*([0-9]+)`)
	if m := rePSS.FindStringSubmatch(output); len(m) > 1 {
		if kb, err := strconv.Atoi(m[1]); err == nil && kb > 0 {
			ramMB = kb / 1024
			return pid, ramMB, true
		}
	}

	reColon := regexp.MustCompile(`(?i)TOTAL:\s*([0-9]+)`)
	if m := reColon.FindStringSubmatch(output); len(m) > 1 {
		if kb, err := strconv.Atoi(m[1]); err == nil && kb > 0 {
			ramMB = kb / 1024
			return pid, ramMB, true
		}
	}

	lines := strings.Split(output, "\n")
	for _, l := range lines {
		trimmed := strings.TrimSpace(l)
		if strings.HasPrefix(strings.ToUpper(trimmed), "TOTAL") {
			fields := strings.Fields(trimmed)
			for _, f := range fields[1:] {
				fClean := strings.Trim(f, ":,")
				if val, err := strconv.Atoi(fClean); err == nil && val > 1000 {
					ramMB = val / 1024
					return pid, ramMB, true
				}
			}
		}
	}

	// If PID was found but ramMB wasn't, check /proc/<pid>/statm directly (with root if available)
	if pid > 0 && ramMB == 0 {
		statmData, sErr := os.ReadFile(fmt.Sprintf("/proc/%d/statm", pid))
		if sErr != nil && checkRoot() {
			if statmOut, rErr := exec.Command("su", "-c", fmt.Sprintf("cat /proc/%d/statm", pid)).Output(); rErr == nil {
				statmData = statmOut
				sErr = nil
			}
		}
		if sErr == nil {
			fields := strings.Fields(string(statmData))
			if len(fields) >= 2 {
				if pages, err := strconv.Atoi(fields[1]); err == nil && pages > 0 {
					ramMB = (pages * 4) / 1024
					return pid, ramMB, true
				}
			}
		}
	}

	return pid, ramMB, ramMB > 0
}

func parsePsOutput(output, pkg string) (int, int, bool) {
	lines := strings.Split(output, "\n")
	pidCol := -1
	rssCol := -1

	for _, line := range lines {
		line = strings.TrimSpace(line)
		if line == "" {
			continue
		}
		fields := strings.Fields(line)

		if pidCol == -1 && (strings.Contains(line, "PID") || strings.Contains(line, "pid")) {
			for i, f := range fields {
				switch strings.ToUpper(f) {
				case "PID":
					pidCol = i
				case "RSS":
					rssCol = i
				}
			}
			continue
		}

		// Match against full package or last segment (e.g. clienb or com.roblox.clienb)
		pkgShort := pkg
		if idx := strings.LastIndex(pkg, "."); idx != -1 {
			pkgShort = pkg[idx+1:]
		}

		if strings.Contains(line, pkg) || strings.Contains(line, pkgShort) {
			if pidCol >= 0 && pidCol < len(fields) {
				if pid, err := strconv.Atoi(fields[pidCol]); err == nil && pid > 0 {
					var rssMB int
					if rssCol >= 0 && rssCol < len(fields) {
						if kb, kErr := strconv.Atoi(fields[rssCol]); kErr == nil && kb > 0 {
							rssMB = kb / 1024
						}
					}
					return pid, rssMB, true
				}
			}

			// Fallback: search fields for integer PID and RSS
			var foundPid int
			var foundRss int
			for _, f := range fields {
				if val, err := strconv.Atoi(f); err == nil && val > 0 {
					if foundPid == 0 && val < 65535 {
						foundPid = val
					} else if val > 10000 && foundRss == 0 { // likely RSS in KB (> 10MB)
						foundRss = val / 1024
					}
				}
			}
			if foundPid > 0 {
				return foundPid, foundRss, true
			}
		}
	}
	return 0, 0, false
}

func getPIDsForPackage(pkg string) []string {
	var results []string
	seen := make(map[string]bool)

	addPID := func(p string) {
		p = strings.TrimSpace(p)
		if p != "" && !seen[p] {
			if _, err := strconv.Atoi(p); err == nil {
				seen[p] = true
				results = append(results, p)
			}
		}
	}

	commands := [][]string{
		{"pidof", pkg},
		{"/system/bin/pidof", pkg},
		{"/system/bin/toybox", "pidof", pkg},
		{"pgrep", "-f", pkg},
		{"/system/bin/pgrep", "-f", pkg},
	}
	if checkRoot() {
		commands = append(commands, [][]string{
			{"su", "-c", "pidof " + pkg},
			{"su", "-c", "pgrep -f " + pkg},
			{"su", "-c", "/system/bin/pidof " + pkg},
		}...)
	}

	for _, cmdArgs := range commands {
		out, err := exec.Command(cmdArgs[0], cmdArgs[1:]...).Output()
		if err == nil {
			for _, f := range strings.Fields(string(out)) {
				addPID(f)
			}
			if len(results) > 0 {
				return results
			}
		}
	}

	return results
}

// getCloneMemoryUsage queries live actual process memory through an Android 10 capable multi-channel pipeline:
// 1. Android OS dumpsys meminfo (bypasses procfs sandboxing)
// 2. Direct procfs /proc/<pid>/statm & root bypass
// 3. System ps / toybox ps inspection
// 4. Thread-safe Telemetry Cache (preserves actual pre-crash metrics on terminated instances)
// 5. Game-specific baseline fallback
func getCloneMemoryUsage(pkg, game string) CloneResourceReport {
	profile := getGameProfile(game)
	report := CloneResourceReport{
		Package:     pkg,
		DisplayName: getCloneDisplayName(pkg),
		IsEstimated: true,
		RAMMB:       profile.EstimatedRAMMB,
		GameProfile: profile.Name,
		Status:      "RUNNING",
	}

	recoveringMu.Lock()
	if recoveringClones[pkg] {
		report.Status = "RECOVERING"
	}
	recoveringMu.Unlock()

	// Channel 1: dumpsys meminfo (Android OS official package memory query)
	dumpsysCmds := [][]string{
		{"dumpsys", "meminfo", pkg},
		{"/system/bin/dumpsys", "meminfo", pkg},
	}
	if checkRoot() {
		dumpsysCmds = append(dumpsysCmds, []string{"su", "-c", "dumpsys meminfo " + pkg})
	}

	for _, cmdArgs := range dumpsysCmds {
		out, err := exec.Command(cmdArgs[0], cmdArgs[1:]...).Output()
		if err == nil && len(out) > 0 {
			outStr := string(out)
			if !strings.Contains(outStr, "No process found") {
				pid, ramMB, ok := parseDumpsysMeminfo(outStr)
				if ok && ramMB > 0 {
					report.PID = pid
					report.RAMMB = ramMB
					report.IsEstimated = false
					report.Status = "RUNNING"
					telemetryStore.Set(pkg, pid, ramMB)
					return report
				}
			}
		}
	}

	// Channel 2: PID resolution + /proc/<pid>/statm
	pids := getPIDsForPackage(pkg)
	for _, pidStr := range pids {
		if pid, err := strconv.Atoi(pidStr); err == nil && pid > 0 {
			report.PID = pid

			statmData, sErr := os.ReadFile(fmt.Sprintf("/proc/%d/statm", pid))
			if sErr != nil && checkRoot() {
				statmOut, rErr := exec.Command("su", "-c", fmt.Sprintf("cat /proc/%d/statm", pid)).Output()
				if rErr == nil {
					statmData = statmOut
					sErr = nil
				}
			}

			if sErr == nil {
				fields := strings.Fields(string(statmData))
				if len(fields) >= 2 {
					if rssPages, pErr := strconv.Atoi(fields[1]); pErr == nil && rssPages > 0 {
						report.RAMMB = (rssPages * 4) / 1024
						report.IsEstimated = false
						report.Status = "RUNNING"
						telemetryStore.Set(pkg, pid, report.RAMMB)
						return report
					}
				}
			}

			// Sub-channel: dumpsys meminfo directly by PID
			pidDumpsysCmds := [][]string{
				{"dumpsys", "meminfo", strconv.Itoa(pid)},
				{"/system/bin/dumpsys", "meminfo", strconv.Itoa(pid)},
			}
			if checkRoot() {
				pidDumpsysCmds = append(pidDumpsysCmds, []string{"su", "-c", fmt.Sprintf("dumpsys meminfo %d", pid)})
			}
			for _, cmdArgs := range pidDumpsysCmds {
				if dOut, dErr := exec.Command(cmdArgs[0], cmdArgs[1:]...).Output(); dErr == nil && len(dOut) > 0 {
					_, dRam, dOk := parseDumpsysMeminfo(string(dOut))
					if dOk && dRam > 0 {
						report.RAMMB = dRam
						report.IsEstimated = false
						report.Status = "RUNNING"
						telemetryStore.Set(pkg, pid, dRam)
						return report
					}
				}
			}
		}
	}

	// Channel 3: ps inspection
	psCmds := [][]string{
		{"ps", "-A"},
		{"/system/bin/ps", "-A"},
		{"/system/bin/toybox", "ps", "-A", "-o", "PID,RSS,NAME"},
	}
	if checkRoot() {
		psCmds = append(psCmds, [][]string{
			{"su", "-c", "ps -A"},
			{"su", "-c", "/system/bin/toybox ps -A -o PID,RSS,NAME"},
			{"su", "-c", "ps -ef"},
		}...)
	}

	for _, cmdArgs := range psCmds {
		out, err := exec.Command(cmdArgs[0], cmdArgs[1:]...).Output()
		if err == nil && len(out) > 0 {
			if pid, ramMB, ok := parsePsOutput(string(out), pkg); ok && pid > 0 {
				report.PID = pid
				if ramMB > 0 {
					report.RAMMB = ramMB
					report.IsEstimated = false
				}
				report.Status = "RUNNING"
				telemetryStore.Set(pkg, pid, report.RAMMB)
				return report
			}
		}
	}

	// Channel 4: Process terminated / crashed / recovering -> use cached actual pre-crash telemetry
	if cached, ok := telemetryStore.Get(pkg); ok && cached.RAMMB > 0 {
		report.PID = cached.PID
		report.RAMMB = cached.RAMMB
		report.IsEstimated = false
		report.Status = "STOPPED"
		return report
	}

	// Channel 5: Fallback baseline estimation
	report.Status = "STOPPED"
	return report
}

// getSortedCloneStatuses returns clone reports sorted logically by Clone index (Clone 1 to N).
func getSortedCloneStatuses() []CloneResourceReport {
	var reports []CloneResourceReport
	for _, pkg := range activePackages {
		cfg := getCloneGameConfig(pkg)
		reports = append(reports, getCloneMemoryUsage(pkg, cfg.Name))
	}
	return reports
}

// ============================================================================
// PACKAGE DETECTION
// ============================================================================

func isPackageInstalled(pkg string) bool {
	// 1. Try pm path
	cmd := exec.Command("pm", "path", pkg)
	out, err := cmd.Output()
	if err == nil && strings.Contains(string(out), "package:") {
		return true
	}

	// 2. Try /system/bin/pm path directly
	cmd2 := exec.Command("/system/bin/pm", "path", pkg)
	out2, err2 := cmd2.Output()
	if err2 == nil && strings.Contains(string(out2), "package:") {
		return true
	}

	// 3. Try pm list packages
	cmd3 := exec.Command("pm", "list", "packages", pkg)
	out3, err3 := cmd3.Output()
	if err3 == nil {
		for _, l := range strings.Split(string(out3), "\n") {
			if strings.TrimSpace(l) == "package:"+pkg {
				return true
			}
		}
	}

	// 4. Try /system/bin/pm list packages
	cmd4 := exec.Command("/system/bin/pm", "list", "packages", pkg)
	out4, err4 := cmd4.Output()
	if err4 == nil {
		for _, l := range strings.Split(string(out4), "\n") {
			if strings.TrimSpace(l) == "package:"+pkg {
				return true
			}
		}
	}

	// 5. Try filesystem checks for app data
	if fi, err := os.Stat("/data/data/" + pkg); err == nil && fi.IsDir() {
		return true
	}
	if fi, err := os.Stat("/sdcard/Android/data/" + pkg); err == nil && fi.IsDir() {
		return true
	}
	if fi, err := os.Stat("/storage/emulated/0/Android/data/" + pkg); err == nil && fi.IsDir() {
		return true
	}

	return false
}

func checkInstalledClones(count int) ([]string, bool) {
	// Determine if running on Android
	isAndroid := false
	if _, err := exec.LookPath("pm"); err == nil {
		isAndroid = true
	} else if _, err := os.Stat("/system/bin/pm"); err == nil {
		isAndroid = true
	} else if _, err := os.Stat("/system/build.prop"); err == nil {
		isAndroid = true
	}

	if !isAndroid {
		return nil, true
	}

	var missing []string
	for i := 0; i < count; i++ {
		pkg := allPackages[i]
		if !isPackageInstalled(pkg) {
			missing = append(missing, fmt.Sprintf("Clone %d", i+1))
		}
	}

	if len(missing) > 0 {
		return missing, false
	}
	return nil, true
}

// ============================================================================
// INPUT & CONFIG HELPERS
// ============================================================================

func initInputReader() {
	go func() {
		var inputSource io.Reader = os.Stdin
		if tty, err := os.Open("/dev/tty"); err == nil {
			inputSource = tty
		}
		scanner := bufio.NewScanner(inputSource)
		for scanner.Scan() {
			inputChan <- scanner.Text()
		}
	}()
}

func readLine() string {
	return <-inputChan
}

func readLineWithTimeout(timeout time.Duration) (string, bool) {
	select {
	case line := <-inputChan:
		return line, true
	case <-time.After(timeout):
		return "", false
	}
}

func drainInput() {
	for {
		select {
		case <-inputChan:
		default:
			return
		}
	}
}

func promptInstruction() {
	fmt.Printf("%s› Enter one letter or number, then press Enter to continue.%s\n", Dim, NC)
}

// Auth Response Structs
type AuthRequest struct {
	Key  string `json:"key"`
	HWID string `json:"hwid"`
}

type AuthResponse struct {
	Success         bool   `json:"success"`
	Error           string `json:"error"`
	Message         string `json:"message"`
	Tier            string `json:"tier"`
	BoundHWID       string `json:"bound_hwid"`
	IsUniversal     bool   `json:"is_universal"`
	DefaultPlaceID  string `json:"default_place_id"`
	DefaultGameName string `json:"default_game_name"`
}

// ============================================================================
// WEBHOOK & NOTIFICATION CONFIGURATION
// ============================================================================

type BannersConfig struct {
	CrashBanner    string `json:"crash_banner"`
	FreezeBanner   string `json:"freeze_banner"`
	RecoveryBanner string `json:"recovery_banner"`
	AskAIBanner    string `json:"ask_ai_banner"`
	ResourceBanner string `json:"resource_banner"`
}

func getDefaultBanners() BannersConfig {
	return BannersConfig{
		CrashBanner:    "",
		FreezeBanner:   "",
		RecoveryBanner: "",
		AskAIBanner:    "",
		ResourceBanner: "",
	}
}

func loadBannersConfig() BannersConfig {
	cfg := getDefaultBanners()
	cfgPath := filepath.Join(getHomeDir(), ".nefhub_banners.json")
	if data, err := os.ReadFile(cfgPath); err == nil {
		_ = json.Unmarshal(data, &cfg)
	} else {
		saveBannersConfig(cfg)
	}
	if strings.Contains(cfg.CrashBanner, "kameskill/autorejoin") {
		cfg.CrashBanner = ""
	}
	if strings.Contains(cfg.FreezeBanner, "kameskill/autorejoin") {
		cfg.FreezeBanner = ""
	}
	if strings.Contains(cfg.RecoveryBanner, "kameskill/autorejoin") {
		cfg.RecoveryBanner = ""
	}
	if strings.Contains(cfg.AskAIBanner, "kameskill/autorejoin") {
		cfg.AskAIBanner = ""
	}
	if strings.Contains(cfg.ResourceBanner, "kameskill/autorejoin") {
		cfg.ResourceBanner = ""
	}
	return cfg
}

func saveBannersConfig(cfg BannersConfig) {
	cfgPath := filepath.Join(getHomeDir(), ".nefhub_banners.json")
	if data, err := json.MarshalIndent(cfg, "", "  "); err == nil {
		_ = os.WriteFile(cfgPath, data, 0644)
	}
}

func loadDiscordMention() string {
	mentionPath := filepath.Join(getHomeDir(), ".nefhub_mention")
	if data, err := os.ReadFile(mentionPath); err == nil {
		return strings.TrimSpace(string(data))
	}
	return ""
}

func saveDiscordMention(mention string) {
	mentionPath := filepath.Join(getHomeDir(), ".nefhub_mention")
	if mention == "" {
		_ = os.Remove(mentionPath)
		return
	}
	_ = os.WriteFile(mentionPath, []byte(mention), 0600)
}

// Discord Webhook Payload with Rich Embeds, Fields, and Banners
type DiscordEmbedField struct {
	Name   string `json:"name"`
	Value  string `json:"value"`
	Inline bool   `json:"inline,omitempty"`
}

type DiscordEmbedMedia struct {
	URL string `json:"url"`
}

type DiscordFooter struct {
	Text string `json:"text"`
}

type DiscordEmbed struct {
	Title       string              `json:"title"`
	Description string              `json:"description,omitempty"`
	Color       int                 `json:"color"`
	Fields      []DiscordEmbedField `json:"fields,omitempty"`
	Image       *DiscordEmbedMedia  `json:"image,omitempty"`
	Thumbnail   *DiscordEmbedMedia  `json:"thumbnail,omitempty"`
	Footer      DiscordFooter       `json:"footer"`
	Timestamp   string              `json:"timestamp,omitempty"`
}

type DiscordWebhookPayload struct {
	Content string         `json:"content,omitempty"`
	Embeds  []DiscordEmbed `json:"embeds"`
}

type WebhookEventType int

const (
	EventGeneral WebhookEventType = iota
	EventCrash
	EventFreeze
	EventRecovery
	EventAskAI
	EventResourceAudit
	EventNetwork
)

func getHomeDir() string {
	home, err := os.UserHomeDir()
	if err != nil || home == "" {
		home = os.Getenv("HOME")
	}
	if home == "" {
		home = "/data/data/com.termux/files/home"
	}
	return home
}

func writeLog(tag, msg string) {
	logMu.Lock()
	defer logMu.Unlock()

	cleanedMsg := cleanSentinelLogLine(msg)
	entry := fmt.Sprintf("[%s] [%s] %s\n", time.Now().Format("2006-01-02 15:04:05"), tag, cleanedMsg)
	f, err := os.OpenFile(LogFileName, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0644)
	if err == nil {
		defer f.Close()
		_, _ = f.WriteString(entry)
	}
}

// sendRichWebhook delivers styled embeds with banner images, resource statistics, and user mentions.
func sendRichWebhook(eventType WebhookEventType, title, message string, color int, fields []DiscordEmbedField) {
	if discordWebhook == "" {
		return
	}

	banners := loadBannersConfig()
	bannerURL := ""
	switch eventType {
	case EventCrash:
		bannerURL = banners.CrashBanner
	case EventFreeze:
		bannerURL = banners.FreezeBanner
	case EventRecovery:
		bannerURL = banners.RecoveryBanner
	case EventAskAI:
		bannerURL = banners.AskAIBanner
	case EventResourceAudit:
		bannerURL = banners.ResourceBanner
	}

	cleanedMsg := cleanSentinelLogLine(message)

	embed := DiscordEmbed{
		Title:       title,
		Description: cleanedMsg,
		Color:       color,
		Fields:      fields,
		Footer: DiscordFooter{
			Text: "Nefarious Hub Sentinel • Resource Guard",
		},
		Timestamp: time.Now().UTC().Format(time.RFC3339),
	}

	if bannerURL != "" {
		embed.Image = &DiscordEmbedMedia{URL: bannerURL}
	}

	payload := DiscordWebhookPayload{
		Embeds: []DiscordEmbed{embed},
	}

	// Mention user only on critical alerts (Crash, Freeze, Recovery, Ask AI)
	if discordMention != "" && (eventType == EventCrash || eventType == EventFreeze || eventType == EventRecovery || eventType == EventAskAI) {
		payload.Content = discordMention
	}

	data, err := json.Marshal(payload)
	if err != nil {
		writeLog("WEBHOOK_ERR", fmt.Sprintf("JSON marshal error: %v", err))
		return
	}

	go func(postData []byte, targetURL string) {
		// 1. Try Go net/http with InsecureSkipVerify (vital for Android Termux root CA handling)
		tr := &http.Transport{
			TLSClientConfig: &tls.Config{
				InsecureSkipVerify: true,
			},
		}
		client := &http.Client{
			Transport: tr,
			Timeout:   8 * time.Second,
		}

		req, err := http.NewRequest("POST", targetURL, bytes.NewBuffer(postData))
		if err == nil {
			req.Header.Set("Content-Type", "application/json")
			req.Header.Set("User-Agent", "Mozilla/5.0 (Linux; Android; Termux) NefariousHub/1.4.3")
			resp, err := client.Do(req)
			if err == nil && resp != nil {
				defer resp.Body.Close()
				if resp.StatusCode >= 200 && resp.StatusCode < 300 {
					return // Delivered successfully!
				}
				respBody, _ := io.ReadAll(resp.Body)
				writeLog("WEBHOOK_ERR", fmt.Sprintf("Discord returned HTTP %d: %s", resp.StatusCode, strings.TrimSpace(string(respBody))))
			} else if err != nil {
				writeLog("WEBHOOK_ERR", fmt.Sprintf("Go HTTP error: %v", err))
			}
		}

		// 2. Fallback to Termux's native curl utility
		cmd := exec.Command("curl", "-s", "-X", "POST",
			"-H", "Content-Type: application/json",
			"-H", "User-Agent: Mozilla/5.0 (Linux; Android; Termux) NefariousHub/1.4.3",
			"--data-binary", "@-",
			targetURL,
		)
		cmd.Stdin = bytes.NewReader(postData)
		out, cErr := cmd.CombinedOutput()
		if cErr != nil {
			writeLog("WEBHOOK_ERR", fmt.Sprintf("curl fallback error: %v (out: %s)", cErr, strings.TrimSpace(string(out))))
		}
	}(data, discordWebhook)
}

// sendWebhook is a backward-compatible wrapper for general events.
func sendWebhook(title, message string, color int) {
	sendRichWebhook(EventGeneral, title, message, color, nil)
}

func sendCrashWebhook(displayName, pkg, game string, res SystemResourceStats, mem CloneResourceReport, timestamp string) {
	memLabel := fmt.Sprintf("%d MB", mem.RAMMB)
	if mem.IsEstimated {
		memLabel = fmt.Sprintf("~%d MB (Estimated - %s)", mem.RAMMB, mem.GameProfile)
	} else if mem.PID > 0 {
		memLabel = fmt.Sprintf("%d MB (Actual RSS before crash - PID %d)", mem.RAMMB, mem.PID)
	} else {
		memLabel = fmt.Sprintf("%d MB (Actual Measured RSS)", mem.RAMMB)
	}

	fields := []DiscordEmbedField{
		{Name: "🎮 Experience", Value: fmt.Sprintf("`%s`", game), Inline: true},
		{Name: "📱 Target Instance", Value: fmt.Sprintf("`%s` (%s)", displayName, pkg), Inline: true},
		{Name: "⚠️ Status", Value: "`CRASHED` (Process Terminated)", Inline: true},
		{Name: "💾 System RAM", Value: fmt.Sprintf("%.1f / %.1f GB Used (%.1f GB Avail - %.0f%%)", res.UsedRAMGB, res.TotalRAMGB, res.AvailableRAMGB, res.RAMUsagePercent), Inline: false},
		{Name: "⚡ CPU Load", Value: fmt.Sprintf("%.1f%% (%d Cores)", res.CPUUsagePercent, res.CPUCores), Inline: true},
		{Name: "📦 Instance Memory", Value: memLabel, Inline: true},
		{Name: "🕒 Event Time", Value: timestamp, Inline: true},
	}

	sendRichWebhook(EventCrash, "🚨 Crash Detected", fmt.Sprintf("**%s** terminated unexpectedly. Initiating automated recovery sequence...", displayName), 15158332, fields)
}

func sendFreezeWebhook(displayName, pkg, game string, res SystemResourceStats, mem CloneResourceReport, timestamp string) {
	memLabel := fmt.Sprintf("%d MB", mem.RAMMB)
	if mem.IsEstimated {
		memLabel = fmt.Sprintf("~%d MB (Estimated - %s)", mem.RAMMB, mem.GameProfile)
	} else if mem.PID > 0 {
		memLabel = fmt.Sprintf("%d MB (Actual RSS before freeze - PID %d)", mem.RAMMB, mem.PID)
	} else {
		memLabel = fmt.Sprintf("%d MB (Actual Measured RSS)", mem.RAMMB)
	}

	fields := []DiscordEmbedField{
		{Name: "🎮 Experience", Value: fmt.Sprintf("`%s`", game), Inline: true},
		{Name: "📱 Target Instance", Value: fmt.Sprintf("`%s` (%s)", displayName, pkg), Inline: true},
		{Name: "❄️ Status", Value: "`FROZEN` (ANR Unresponsive)", Inline: true},
		{Name: "💾 System RAM", Value: fmt.Sprintf("%.1f / %.1f GB Used (%.1f GB Avail - %.0f%%)", res.UsedRAMGB, res.TotalRAMGB, res.AvailableRAMGB, res.RAMUsagePercent), Inline: false},
		{Name: "⚡ CPU Load", Value: fmt.Sprintf("%.1f%% (%d Cores)", res.CPUUsagePercent, res.CPUCores), Inline: true},
		{Name: "📦 Instance Memory", Value: memLabel, Inline: true},
		{Name: "🕒 Event Time", Value: timestamp, Inline: true},
	}

	sendRichWebhook(EventFreeze, "❄️ Freeze Detected (ANR)", fmt.Sprintf("**%s** stopped responding. Force-rebooting clone client engine...", displayName), 15105570, fields)
}

func sendRecoveryWebhook(displayName, pkg, game string, res SystemResourceStats, mem CloneResourceReport) {
	memLabel := fmt.Sprintf("%d MB", mem.RAMMB)
	if mem.IsEstimated {
		memLabel = fmt.Sprintf("~%d MB (Estimated - %s)", mem.RAMMB, mem.GameProfile)
	} else if mem.PID > 0 {
		memLabel = fmt.Sprintf("%d MB (Actual RSS - PID %d)", mem.RAMMB, mem.PID)
	} else {
		memLabel = fmt.Sprintf("%d MB (Actual Measured RSS)", mem.RAMMB)
	}

	fields := []DiscordEmbedField{
		{Name: "🎮 Experience", Value: fmt.Sprintf("`%s`", game), Inline: true},
		{Name: "📱 Target Instance", Value: fmt.Sprintf("`%s`", displayName), Inline: true},
		{Name: "✅ Status", Value: "`ONLINE & SYNCHRONIZED`", Inline: true},
		{Name: "💾 System RAM", Value: fmt.Sprintf("%.1f / %.1f GB Used (%.1f GB Avail)", res.UsedRAMGB, res.TotalRAMGB, res.AvailableRAMGB), Inline: false},
		{Name: "⚡ CPU Load", Value: fmt.Sprintf("%.1f%% (%d Cores)", res.CPUUsagePercent, res.CPUCores), Inline: true},
		{Name: "📦 Instance Memory", Value: memLabel, Inline: true},
		{Name: "🕒 Restored At", Value: time.Now().Format("2006-01-02 15:04:05"), Inline: true},
	}

	sendRichWebhook(EventRecovery, "✅ Instance Recovered", fmt.Sprintf("**%s** is back online and resynchronized with **%s**.", displayName, game), 3066993, fields)
}

func sendSessionStartWebhook() {
	if discordWebhook == "" {
		return
	}
	res := getSystemResources()
	fields := []DiscordEmbedField{
		{Name: "🎮 Target Experience", Value: func() string { if len(cloneGameConfigs) > 1 { var names []string; for _, c := range cloneGameConfigs { names = append(names, c.Name) }; unique := map[string]bool{}; var uniq []string; for _, n := range names { if !unique[n] { unique[n] = true; uniq = append(uniq, n) } }; if len(uniq) > 1 { return "`Mixed: " + strings.Join(uniq, " / ") + "`" } }; return fmt.Sprintf("`%s`", gameName) }(), Inline: true},
		{Name: "📱 Active Instances", Value: fmt.Sprintf("`%d Clone%s Online`", cloneCount, plural(cloneCount)), Inline: true},
		{Name: "🛡️ Sentinel Guard", Value: "`ACTIVE (24/7 Watchdog)`", Inline: true},
		{Name: "🧹 System Optimizer", Value: fmt.Sprintf("`%s (+%d MB Freed)`", cleanedModeDesc, cleanedRAMFreedMB), Inline: true},
		{Name: "💾 System Memory", Value: fmt.Sprintf("%.1f / %.1f GB (%.0f%% Used)", res.UsedRAMGB, res.TotalRAMGB, res.RAMUsagePercent), Inline: false},
		{Name: "⚡ CPU Cores & Load", Value: fmt.Sprintf("%.1f%% (%d Cores)", res.CPUUsagePercent, res.CPUCores), Inline: true},
		{Name: "🕒 Started At", Value: time.Now().Format("2006-01-02 15:04:05"), Inline: true},
	}
	sendRichWebhook(EventGeneral, "🚀 Nefarious Hub — Session Started",
		func() string { isMix := false; if len(cloneGameConfigs) > 1 { for i := 1; i < len(cloneGameConfigs); i++ { if cloneGameConfigs[i].Name != cloneGameConfigs[0].Name { isMix = true; break } } }; if isMix { var names []string; for i, c := range cloneGameConfigs { names = append(names, fmt.Sprintf("Clone %d → %s", i+1, c.Name)) }; return fmt.Sprintf("**%d Roblox instances** started in Mixed Mode:\\n%s", cloneCount, strings.Join(names, "\\n")) }; return fmt.Sprintf("All **%d Roblox instances** are running and synchronized with **%s**.", cloneCount, gameName) }(),
		3066993, fields)
}

func sendAskAIWebhook(player, cloneParam, query string) {
	if discordWebhook == "" {
		return
	}
	res := getSystemResources()
	cloneLabel := "Clone (Active)"
	if cloneParam != "" {
		cloneLabel = fmt.Sprintf("Clone %s", cloneParam)
	}

	fields := []DiscordEmbedField{
		{Name: "📱 Instance", Value: fmt.Sprintf("`%s`", cloneLabel), Inline: true},
		{Name: "👤 Player", Value: fmt.Sprintf("`%s`", player), Inline: true},
		{Name: "💾 System RAM", Value: fmt.Sprintf("%.1f / %.1f GB (%.0f%%)", res.UsedRAMGB, res.TotalRAMGB, res.RAMUsagePercent), Inline: true},
		{Name: "❓ Query / Prompt", Value: fmt.Sprintf("```%s```", truncate(query, 1000)), Inline: false},
	}

	sendRichWebhook(EventAskAI, "🤖 Ask AI Assistant", fmt.Sprintf("New AI assistance request dispatched from `%s`.", player), 3447003, fields)
}

// startResourceMonitor runs a periodic resource health audit every 5 minutes,
// and sends an initial audit report shortly after startup once instances stabilize.
func startResourceMonitor() {
	runAudit := func() {
		if discordWebhook == "" || !isInternetConnected() {
			return
		}

		res := getSystemResources()
		if res.TotalRAMMB == 0 {
			return
		}

		var cloneLines []string
		for _, pkg := range activePackages {
			rep := getCloneMemoryUsage(pkg, gameName)
			tag := fmt.Sprintf("`%s`", rep.DisplayName)
			if rep.IsEstimated {
				cloneLines = append(cloneLines, fmt.Sprintf("• %s: ~%d MB *(Estimated - %s)*", tag, rep.RAMMB, rep.GameProfile))
			} else if rep.PID > 0 {
				cloneLines = append(cloneLines, fmt.Sprintf("• %s: %d MB *(Actual RSS - PID %d)*", tag, rep.RAMMB, rep.PID))
			} else {
				cloneLines = append(cloneLines, fmt.Sprintf("• %s: %d MB *(Actual RSS)*", tag, rep.RAMMB))
			}
		}

		cloneSummary := strings.Join(cloneLines, "\n")
		if cloneSummary == "" {
			cloneSummary = "*No active clones monitored*"
		}

		fields := []DiscordEmbedField{
			{Name: "💾 System RAM", Value: fmt.Sprintf("%.1f / %.1f GB Used (%.1f GB Avail - %.0f%%)", res.UsedRAMGB, res.TotalRAMGB, res.AvailableRAMGB, res.RAMUsagePercent), Inline: false},
			{Name: "⚡ CPU Load", Value: fmt.Sprintf("%.1f%% (%d Cores)", res.CPUUsagePercent, res.CPUCores), Inline: true},
			{Name: "🛡️ Sentinel Status", Value: fmt.Sprintf("%d Clones Active", len(activePackages)), Inline: true},
			{Name: "📱 Monitored Instances", Value: cloneSummary, Inline: false},
			{Name: "🎮 Target Experience", Value: fmt.Sprintf("`%s`", truncate(gameName, 28)), Inline: true}, // gameName = first/only game
			{Name: "🕒 Report Time", Value: time.Now().Format("2006-01-02 15:04:05"), Inline: true},
		}

		sendRichWebhook(EventResourceAudit, "📊 Periodic Resource Health Monitor (5m)",
			"Automated 5-minute system and instance resource telemetry.",
			5793266, fields)
	}

	// Send initial audit report 25 seconds after sentinel begins so the user immediately sees live metrics
	go func() {
		time.Sleep(25 * time.Second)
		runAudit()
	}()

	ticker := time.NewTicker(5 * time.Minute)
	defer ticker.Stop()

	for range ticker.C {
		runAudit()
	}
}

// startTelemetrySampler continually refreshes clone memory telemetry every 5 seconds
// so crashes and freeze events always capture live actual measured memory and the
// on-screen dashboard updates to real-time RAM metrics.
func startTelemetrySampler() {
	ticker := time.NewTicker(5 * time.Second)
	lastSampledRAM := make(map[string]int)
	go func() {
		for range ticker.C {
			if !isMonitoringActive {
				continue
			}
			updated := false
			for _, pkg := range activePackages {
				rep := getCloneMemoryUsage(pkg, gameName)

				// Telemetry Health Store: updates measured RAM and PID without false-positive procfs crash triggers
				cloneHealthMu.Lock()
				h, exists := cloneHealthStore[pkg]
				if !exists {
					h = &cloneHealthInfo{launchedAt: time.Now()}
					cloneHealthStore[pkg] = h
				}

				if rep.PID > 0 && rep.RAMMB > 0 {
					h.lastRAM = rep.RAMMB
					h.lastPID = rep.PID
					h.stagnantCycles = 0
				}
				cloneHealthMu.Unlock()

				if !rep.IsEstimated && rep.RAMMB > 0 {
					lastRAM := lastSampledRAM[pkg]
					// Only redraw when measured RAM delta is significant (>= 15 MB) to eliminate visual flicker
					delta := rep.RAMMB - lastRAM
					if delta < 0 {
						delta = -delta
					}
					if delta >= 15 || lastRAM == 0 {
						lastSampledRAM[pkg] = rep.RAMMB
						updated = true
					}
				}
			}
			if updated {
				dashboardMu.Lock()
				active := isMonitoringActive
				hasCountdown := currentDashboard.ActionStep != ""
				dashboardMu.Unlock()
				if active && !hasCountdown {
					drawSummaryCard()
				}
			}
		}
	}()
}

// ============================================================================
// HARDWARE ID & DEVICE INTEGRITY
// ============================================================================

func getDeviceHWID() string {
	readCmd := func(name string, args ...string) string {
		out, err := exec.Command(name, args...).Output()
		if err != nil {
			return ""
		}
		return strings.TrimSpace(string(out))
	}

	aid := readCmd("settings", "get", "secure", "android_id")
	model := readCmd("getprop", "ro.product.model")
	build := readCmd("getprop", "ro.build.id")
	serial := readCmd("getprop", "ro.serialno")

	raw := fmt.Sprintf("%s_%s_%s_%s", aid, model, build, serial)
	if aid == "" && model == "" {
		unameOut, _ := exec.Command("uname", "-a").Output()
		whoamiOut, _ := exec.Command("whoami").Output()
		raw = fmt.Sprintf("%s_%s", strings.TrimSpace(string(unameOut)), strings.TrimSpace(string(whoamiOut)))
	}

	hash := sha256.Sum256([]byte(raw))
	hwidHex := fmt.Sprintf("%x", hash)
	var finalHWID string
	if len(hwidHex) >= 16 {
		finalHWID = strings.ToUpper(hwidHex[:16])
	} else {
		finalHWID = strings.ToUpper(hwidHex)
	}
	_ = os.WriteFile("/sdcard/nefarious_hwid.txt", []byte(finalHWID), 0644)
	_ = os.WriteFile("/sdcard/Delta/nefarious_hwid.txt", []byte(finalHWID), 0644)

	// Clean up legacy files
	cleanTargets := []string{
		"/sdcard/Delta/autoexec/nefarious_client.lua",
		"/sdcard/nefarious_client.lua",
		"/storage/emulated/0/Delta/autoexec/nefarious_client.lua",
	}
	for _, pkg := range allPackages {
		cleanTargets = append(cleanTargets, fmt.Sprintf("/sdcard/Android/data/%s/files/Delta/autoexec/nefarious_client.lua", pkg))
	}
	for _, target := range cleanTargets {
		_ = os.Remove(target)
	}

	return finalHWID
}

// ============================================================================
// UI RENDERING & CARDS (DYNAMIC CENTERED BOX SYSTEM WITH SMOOTH CURVES)
// ============================================================================

var ansiRegex = regexp.MustCompile(`\x1b\[[0-9;]*[a-zA-Z]`)

func stripANSI(s string) string {
	return ansiRegex.ReplaceAllString(s, "")
}

func visibleWidth(s string) int {
	return utf8.RuneCountInString(stripANSI(s))
}

func truncateVisible(s string, maxCols int) string {
	if maxCols <= 0 {
		return ""
	}
	clean := stripANSI(s)
	runes := []rune(clean)
	if len(runes) <= maxCols {
		return clean
	}
	if maxCols <= 3 {
		return string(runes[:maxCols])
	}
	return string(runes[:maxCols-3]) + "..."
}

func wrapText(s string, width int) []string {
	if width <= 0 {
		return []string{s}
	}
	clean := stripANSI(s)
	words := strings.Fields(clean)
	if len(words) == 0 {
		return []string{clean}
	}

	var res []string
	var curr strings.Builder
	currLen := 0

	for _, w := range words {
		wLen := utf8.RuneCountInString(w)
		if currLen == 0 {
			if wLen > width {
				runes := []rune(w)
				for len(runes) > 0 {
					take := width
					if take > len(runes) {
						take = len(runes)
					}
					res = append(res, string(runes[:take]))
					runes = runes[take:]
				}
				continue
			}
			curr.WriteString(w)
			currLen = wLen
		} else if currLen+1+wLen <= width {
			curr.WriteString(" ")
			curr.WriteString(w)
			currLen += 1 + wLen
		} else {
			res = append(res, curr.String())
			curr.Reset()
			if wLen > width {
				runes := []rune(w)
				for len(runes) > 0 {
					take := width
					if take > len(runes) {
						take = len(runes)
					}
					res = append(res, string(runes[:take]))
					runes = runes[take:]
				}
				currLen = 0
			} else {
				curr.WriteString(w)
				currLen = wLen
			}
		}
	}
	if currLen > 0 {
		res = append(res, curr.String())
	}
	return res
}

func detectTerminalSize() (int, int) {
	// 1. Check environment variables COLUMNS and LINES
	if cols, err := strconv.Atoi(os.Getenv("COLUMNS")); err == nil && cols > 10 {
		if lines, err2 := strconv.Atoi(os.Getenv("LINES")); err2 == nil && lines > 5 {
			return cols, lines
		}
	}

	// 2. Try stty size with /dev/tty or stdout/stderr redirection (standard for Android Termux)
	sttyCmds := []string{
		"stty size < /dev/tty 2>/dev/null",
		"stty size <&1 2>/dev/null",
		"stty size <&2 2>/dev/null",
		"/system/bin/stty size < /dev/tty 2>/dev/null",
		"/system/bin/stty size <&1 2>/dev/null",
		"/system/bin/stty size <&2 2>/dev/null",
		"stty size 2>/dev/null",
	}
	for _, cmdStr := range sttyCmds {
		if out, err := exec.Command("sh", "-c", cmdStr).Output(); err == nil {
			parts := strings.Fields(string(out))
			if len(parts) >= 2 {
				h, errH := strconv.Atoi(parts[0])
				w, errW := strconv.Atoi(parts[1])
				if errH == nil && errW == nil && w > 10 && h > 5 {
					return w, h
				}
			}
		}
	}

	// 3. Try tput cols / tput lines with /dev/tty or stdout/stderr
	tputCmds := []string{
		"tput cols < /dev/tty 2>/dev/null",
		"tput cols <&1 2>/dev/null",
		"tput cols <&2 2>/dev/null",
		"tput cols 2>/dev/null",
	}
	for _, cmdStr := range tputCmds {
		if outW, err := exec.Command("sh", "-c", cmdStr).Output(); err == nil {
			if w, err := strconv.Atoi(strings.TrimSpace(string(outW))); err == nil && w > 10 {
				h := 24
				if outH, err := exec.Command("sh", "-c", "tput lines < /dev/tty 2>/dev/null || tput lines <&1 2>/dev/null || tput lines 2>/dev/null").Output(); err == nil {
					if hVal, err := strconv.Atoi(strings.TrimSpace(string(outH))); err == nil && hVal > 5 {
						h = hVal
					}
				}
				return w, h
			}
		}
	}

	// 4. Android Developer Options "Smallest Width" (dp) Detection via wm size & density
	// Uses root / shell to read exact hardware display geometry and compute character capacity
	var screenPxW int
	wmSizeCmds := []string{
		"wm size 2>/dev/null",
		"/system/bin/wm size 2>/dev/null",
	}
	if checkRoot() {
		wmSizeCmds = append(wmSizeCmds, "su -c 'wm size' 2>/dev/null")
	}
	for _, cmdStr := range wmSizeCmds {
		if out, err := exec.Command("sh", "-c", cmdStr).Output(); err == nil {
			reSize := regexp.MustCompile(`([0-9]+)x([0-9]+)`)
			if m := reSize.FindStringSubmatch(string(out)); len(m) >= 3 {
				w, _ := strconv.Atoi(m[1])
				h, _ := strconv.Atoi(m[2])
				if w > 0 && h > 0 {
					if w < h {
						screenPxW = w
					} else {
						screenPxW = h
					}
					break
				}
			}
		}
	}

	var density int
	wmDenCmds := []string{
		"wm density 2>/dev/null",
		"/system/bin/wm density 2>/dev/null",
	}
	if checkRoot() {
		wmDenCmds = append(wmDenCmds, "su -c 'wm density' 2>/dev/null")
	}
	for _, cmdStr := range wmDenCmds {
		if out, err := exec.Command("sh", "-c", cmdStr).Output(); err == nil {
			reDen := regexp.MustCompile(`density:\s*([0-9]+)`)
			if m := reDen.FindStringSubmatch(string(out)); len(m) > 1 {
				if d, err := strconv.Atoi(m[1]); err == nil && d > 0 {
					density = d
					break
				}
			}
		}
	}

	// Smallest width in DP = (px * 160) / density
	if screenPxW > 0 && density > 0 {
		swDp := (screenPxW * 160) / density
		// Termux standard font consumes ~8.2 dp per character column
		calcCols := int(float64(swDp) / 8.2)
		if calcCols >= 36 && calcCols <= 240 {
			return calcCols, 24
		}
	}

	// 5. Native Termux Baseline (80 columns, 24 rows)
	return 80, 24
}

func calculateBoxDimensions(boxHeight int) (boxWidth, leftPadding, topPadding int) {
	termW, termH := detectTerminalSize()

	preferredBoxWidth := DASHBOARD_MAX_WIDTH
	minimumBoxWidth := DASHBOARD_MIN_WIDTH
	safetyMargin := TERMINAL_SAFETY_MARGIN

	avail := termW - safetyMargin
	if avail < 10 {
		avail = termW
	}

	boxWidth = preferredBoxWidth
	if boxWidth > avail {
		boxWidth = avail
	}
	if boxWidth < minimumBoxWidth {
		boxWidth = minimumBoxWidth
	}
	// Absolute ceiling: never exceed physical terminal width
	if boxWidth > termW {
		boxWidth = termW
	}

	leftPadding = 0
	if CENTER_DASHBOARD && termW > boxWidth {
		leftPadding = (termW - boxWidth) / 2
	}

	// The box must always satisfy: left_padding + box_width <= terminal_width
	if leftPadding+boxWidth > termW {
		leftPadding = termW - boxWidth
		if leftPadding < 0 {
			leftPadding = 0
		}
	}

	// Vertical positioning: strictly disabled on mobile/small terminals (< 38 rows)
	topPadding = 0
	if CENTER_DASHBOARD_VERTICALLY && termH >= 38 && termH > boxHeight+8 {
		topPadding = (termH - boxHeight) / 4
		if topPadding > 2 {
			topPadding = 2
		}
	}

	return boxWidth, leftPadding, topPadding
}

type RowType int

const (
	RowHeader RowType = iota
	RowSubtitle
	RowKeyValue
	RowSeparator
	RowCentered
	RowStatus
	RowBlank
)

type BoxRow struct {
	Type        RowType
	Label       string
	LabelColor  string
	Value       string
	ValueColor  string
	RightText   string
	RightColor  string
	CustomText  string
	CustomColor string
	PrefixIcon  string
	PrefixColor string
}

type DashboardEventInfo struct {
	Status      string
	StatusColor string
	EventTag    string
	EventDesc   string
	EventRAM    string
	EventTime   string
	HasEvent    bool
	ActionStep  string
	ActionColor string
	QueueInfo   string
}

var (
	dashboardMu       sync.Mutex
	currentDashboard  = DashboardEventInfo{
		Status:      "Monitoring Active",
		StatusColor: Green,
	}
	isMonitoringActive = false
)

func setDashboardStatus(status string, color string) {
	dashboardMu.Lock()
	if status != "" {
		currentDashboard.Status = status
	}
	if color != "" {
		currentDashboard.StatusColor = color
	}
	active := isMonitoringActive
	dashboardMu.Unlock()

	if active {
		drawSummaryCard()
	}
}

func clearDashboardEvent() {
	dashboardMu.Lock()
	currentDashboard.HasEvent = false
	currentDashboard.EventTag = ""
	currentDashboard.EventDesc = ""
	currentDashboard.EventRAM = ""
	currentDashboard.EventTime = ""
	currentDashboard.ActionStep = ""
	currentDashboard.QueueInfo = ""
	active := isMonitoringActive
	dashboardMu.Unlock()

	if active {
		drawSummaryCard()
	}
}

func setDashboardEvent(status, statusColor, eventTag, eventDesc, eventRAM, eventTime string) {
	dashboardMu.Lock()
	if status != "" {
		currentDashboard.Status = status
	}
	if statusColor != "" {
		currentDashboard.StatusColor = statusColor
	}
	if eventTag != "" {
		currentDashboard.EventTag = eventTag
		currentDashboard.EventDesc = eventDesc
		currentDashboard.EventRAM = eventRAM
		currentDashboard.EventTime = eventTime
		currentDashboard.HasEvent = true
	}
	active := isMonitoringActive
	dashboardMu.Unlock()

	if active {
		drawSummaryCard()
	}
}

func initResizeWatcher() {
	winchChan := make(chan os.Signal, 1)
	signal.Notify(winchChan, syscall.Signal(28)) // SIGWINCH on Linux / Android Termux
	go func() {
		for range winchChan {
			onTerminalResize()
		}
	}()
}

func onTerminalResize() {
	dashboardMu.Lock()
	active := isMonitoringActive
	dashboardMu.Unlock()
	if active {
		drawSummaryCard()
	}
}

func renderCenteredBox(title string, rows []BoxRow, termWidth int, termHeight int, borderColor string) string {
	boxWidth, leftPad, topPad := calculateBoxDimensions(len(rows) + 2)
	padStr := strings.Repeat(" ", leftPad)

	innerSpan := boxWidth - 2
	if innerSpan < 1 {
		innerSpan = 1
	}

	innerPad := 2
	if innerSpan <= 36 {
		innerPad = 1
	}
	availInner := innerSpan - (innerPad * 2)
	if availInner < 1 {
		availInner = 1
	}

	var sb strings.Builder

	// Top padding if vertically centered
	for i := 0; i < topPad; i++ {
		sb.WriteString("\n")
	}

	if borderColor == "" || borderColor == Gray {
		borderColor = Cyan
	}

	// Top Border with double-line corners: ╔ ╗
	sb.WriteString(padStr)
	sb.WriteString(borderColor)
	sb.WriteString("╔")
	sb.WriteString(strings.Repeat("═", innerSpan))
	sb.WriteString("╗")
	sb.WriteString(NC)
	sb.WriteString("\n")

	for _, r := range rows {
		switch r.Type {
		case RowSeparator:
			sb.WriteString(padStr)
			sb.WriteString(borderColor)
			sb.WriteString("╠")
			sb.WriteString(strings.Repeat("═", innerSpan))
			sb.WriteString("╣")
			sb.WriteString(NC)
			sb.WriteString("\n")

		case RowHeader:
			leftVis := r.PrefixIcon + r.Label
			leftLen := visibleWidth(leftVis)
			rightVis := r.RightText
			rightLen := visibleWidth(rightVis)

			if leftLen+rightLen+1 > availInner {
				availForLeft := availInner - rightLen - 1
				if availForLeft < 6 {
					availForLeft = 6
				}
				leftVis = truncateVisible(leftVis, availForLeft)
				leftLen = visibleWidth(leftVis)
			}

			gap := availInner - leftLen - rightLen
			if gap < 0 {
				gap = 0
			}

			sb.WriteString(padStr)
			sb.WriteString(borderColor)
			sb.WriteString("║")
			sb.WriteString(NC)
			sb.WriteString(strings.Repeat(" ", innerPad))

			if r.PrefixIcon != "" {
				sb.WriteString(r.PrefixColor)
				sb.WriteString(r.PrefixIcon)
				sb.WriteString(NC)
			}
			sb.WriteString(r.LabelColor)
			sb.WriteString(r.Label)
			sb.WriteString(NC)

			sb.WriteString(strings.Repeat(" ", gap))

			if r.RightText != "" {
				sb.WriteString(r.RightColor)
				sb.WriteString(r.RightText)
				sb.WriteString(NC)
			}

			sb.WriteString(strings.Repeat(" ", innerPad))
			sb.WriteString(borderColor)
			sb.WriteString("║")
			sb.WriteString(NC)
			sb.WriteString("\n")

		case RowSubtitle, RowCentered:
			text := r.CustomText
			var linesToPrint []string
			if visibleWidth(text) > availInner && WRAP_LONG_VALUES && availInner >= 10 {
				linesToPrint = wrapText(text, availInner)
			} else if visibleWidth(text) > availInner {
				linesToPrint = []string{truncateVisible(text, availInner)}
			} else {
				linesToPrint = []string{text}
			}

			for _, lText := range linesToPrint {
				txtLen := visibleWidth(lText)
				var leftSpaces, rightSpaces int
				if r.Type == RowCentered {
					leftSpaces = (availInner - txtLen) / 2
					rightSpaces = availInner - txtLen - leftSpaces
				} else {
					leftSpaces = 0
					rightSpaces = availInner - txtLen
				}
				if leftSpaces < 0 {
					leftSpaces = 0
				}
				if rightSpaces < 0 {
					rightSpaces = 0
				}

				sb.WriteString(padStr)
				sb.WriteString(borderColor)
				sb.WriteString("║")
				sb.WriteString(NC)
				sb.WriteString(strings.Repeat(" ", innerPad+leftSpaces))
				sb.WriteString(r.CustomColor)
				sb.WriteString(lText)
				sb.WriteString(NC)
				sb.WriteString(strings.Repeat(" ", rightSpaces+innerPad))
				sb.WriteString(borderColor)
				sb.WriteString("║")
				sb.WriteString(NC)
				sb.WriteString("\n")
			}

		case RowKeyValue, RowStatus:
			lbl := r.Label
			val := r.Value
			lblLen := visibleWidth(lbl)
			availVal := availInner - lblLen
			if availVal < 4 {
				availVal = 4
			}

			if visibleWidth(val) > availVal {
				if WRAP_LONG_VALUES && availVal >= 10 {
					chunks := wrapText(val, availVal)
					for i, ch := range chunks {
						chLen := visibleWidth(ch)
						chGap := availVal - chLen
						if chGap < 0 {
							chGap = 0
						}

						sb.WriteString(padStr)
						sb.WriteString(borderColor)
						sb.WriteString("║")
						sb.WriteString(NC)
						sb.WriteString(strings.Repeat(" ", innerPad))

						if i == 0 {
							sb.WriteString(r.LabelColor)
							sb.WriteString(lbl)
							sb.WriteString(NC)
						} else {
							sb.WriteString(strings.Repeat(" ", lblLen))
						}

						sb.WriteString(r.ValueColor)
						sb.WriteString(ch)
						sb.WriteString(NC)
						sb.WriteString(strings.Repeat(" ", chGap))
						sb.WriteString(strings.Repeat(" ", innerPad))
						sb.WriteString(borderColor)
						sb.WriteString("║")
						sb.WriteString(NC)
						sb.WriteString("\n")
					}
					continue
				} else if SHORTEN_LONG_VALUES {
					val = truncateVisible(val, availVal)
				}
			}

			valLen := visibleWidth(val)
			gap := availInner - lblLen - valLen
			if gap < 0 {
				gap = 0
			}

			sb.WriteString(padStr)
			sb.WriteString(borderColor)
			sb.WriteString("║")
			sb.WriteString(NC)
			sb.WriteString(strings.Repeat(" ", innerPad))
			sb.WriteString(r.LabelColor)
			sb.WriteString(lbl)
			sb.WriteString(NC)
			sb.WriteString(r.ValueColor)
			sb.WriteString(val)
			sb.WriteString(NC)
			sb.WriteString(strings.Repeat(" ", gap))
			sb.WriteString(strings.Repeat(" ", innerPad))
			sb.WriteString(borderColor)
			sb.WriteString("║")
			sb.WriteString(NC)
			sb.WriteString("\n")

		case RowBlank:
			sb.WriteString(padStr)
			sb.WriteString(borderColor)
			sb.WriteString("║")
			sb.WriteString(NC)
			sb.WriteString(strings.Repeat(" ", innerSpan))
			sb.WriteString(borderColor)
			sb.WriteString("║")
			sb.WriteString(NC)
			sb.WriteString("\n")
		}
	}

	// Bottom Border with double-line corners: ╚ ╝
	sb.WriteString(padStr)
	sb.WriteString(borderColor)
	sb.WriteString("╚")
	sb.WriteString(strings.Repeat("═", innerSpan))
	sb.WriteString("╝")
	sb.WriteString(NC)
	sb.WriteString("\n")

	return sb.String()
}

func clearTerminal() {
	// 1. ANSI escape sequence: move cursor home, clear visible screen, and wipe scrollback buffer
	fmt.Print("\033[H\033[2J\033[3J")

	// 2. Invoke platform native clear command to ensure terminfo and terminal scrollback are cleanly reset
	clearCmd := "clear"
	if runtime.GOOS == "windows" {
		clearCmd = "cls"
	}
	cmd := exec.Command(clearCmd)
	cmd.Stdout = os.Stdout
	_ = cmd.Run()
}

func drawBanner() {
	termW, termH := detectTerminalSize()

	rows := []BoxRow{
		{
			Type:        RowHeader,
			PrefixIcon:  "◆ ",
			PrefixColor: Cyan,
			Label:       "NEFARIUS HUB",
			LabelColor:  Bold + Cyan,
			RightText:   "v" + ScriptVersion,
			RightColor:  White,
		},
		{
			Type:        RowSubtitle,
			CustomText:  "Sentinel & Multi-Instance Guard",
			CustomColor: Dim,
		},
	}

	if licenseKey != "" {
		hwidVal := myHWID
		if isUniversalKey {
			hwidVal = "UNIVERSAL (Multi-Device)"
		}
		rows = append(rows,
			BoxRow{Type: RowSeparator},
			BoxRow{
				Type:       RowKeyValue,
				Label:      "License : ",
				LabelColor: Gray,
				Value:      licenseKey,
				ValueColor: White,
			},
			BoxRow{
				Type:       RowKeyValue,
				Label:      "Tier    : ",
				LabelColor: Gray,
				Value:      licenseDuration,
				ValueColor: Green,
			},
			BoxRow{
				Type:       RowKeyValue,
				Label:      "HWID    : ",
				LabelColor: Gray,
				Value:      hwidVal,
				ValueColor: Cyan,
			},
		)
	}

	rows = append(rows,
		BoxRow{Type: RowSeparator},
		BoxRow{
			Type:       RowKeyValue,
			Label:      "Script Devs : ",
			LabelColor: Gray,
			Value:      "@NightWitch, @Eysdi",
			ValueColor: White,
		},
		BoxRow{
			Type:       RowKeyValue,
			Label:      "Clone Credit: ",
			LabelColor: Gray,
			Value:      "@Jep",
			ValueColor: Cyan,
		},
		BoxRow{
			Type:       RowKeyValue,
			Label:      "Invite Link : ",
			LabelColor: Gray,
			Value:      DiscordInviteURL,
			ValueColor: Cyan,
		},
	)

	box := renderCenteredBox("BANNER", rows, termW, termH, Gray)
	clearTerminal()
	fmt.Print(box)
}

func getMenuLeftPad() string {
	_, leftPad, _ := calculateBoxDimensions(10)
	return strings.Repeat(" ", leftPad)
}

func drawStepCard(stepTitle, stepSubtitle string, rows []BoxRow) {
	termW, termH := detectTerminalSize()

	cardRows := []BoxRow{
		{
			Type:        RowHeader,
			PrefixIcon:  "◆ ",
			PrefixColor: Cyan,
			Label:       stepTitle,
			LabelColor:  Bold + White,
			RightText:   "v" + ScriptVersion,
			RightColor:  Dim,
		},
	}
	if stepSubtitle != "" {
		cardRows = append(cardRows, BoxRow{
			Type:        RowSubtitle,
			CustomText:  stepSubtitle,
			CustomColor: Cyan,
		})
	}
	if len(rows) > 0 {
		cardRows = append(cardRows, BoxRow{Type: RowSeparator})
		cardRows = append(cardRows, rows...)
	}

	box := renderCenteredBox(stepTitle, cardRows, termW, termH, Gray)
	clearTerminal()
	fmt.Print(box)
}

func drawAlertCard(cardType, title, line1, line2, line3 string) {
	borderColor := Gray
	titleColor := White
	switch cardType {
	case "ERROR":
		borderColor = Red
		titleColor = Red
	case "WARN":
		borderColor = Amber
		titleColor = Amber
	case "SUCCESS":
		borderColor = Green
		titleColor = Green
	}

	termW, termH := detectTerminalSize()
	rows := []BoxRow{
		{
			Type:        RowCentered,
			CustomText:  title,
			CustomColor: Bold + titleColor,
		},
	}
	if line1 != "" || line2 != "" || line3 != "" {
		rows = append(rows, BoxRow{Type: RowSeparator})
		if line1 != "" {
			rows = append(rows, BoxRow{Type: RowSubtitle, CustomText: line1, CustomColor: White})
		}
		if line2 != "" {
			rows = append(rows, BoxRow{Type: RowSubtitle, CustomText: line2, CustomColor: White})
		}
		if line3 != "" {
			rows = append(rows, BoxRow{Type: RowSubtitle, CustomText: line3, CustomColor: White})
		}
	}
	fmt.Print(renderCenteredBox("ALERT", rows, termW, termH, borderColor))
}

// drawSummaryCard renders the Session Pre-Flight with live RAM, CPU, and game profile metrics.
func drawSummaryCard() {
	renderMu.Lock()
	defer renderMu.Unlock()

	res := getSystemResources()
	profile := getGameProfile(gameName)
	termW, termH := detectTerminalSize()

	tierDisplay := licenseDuration
	if tierDisplay == "" {
		tierDisplay = "Free"
	}

	rows := []BoxRow{
		{
			Type:        RowHeader,
			PrefixIcon:  "◆ ",
			PrefixColor: Cyan,
			Label:       "NEFARIUS HUB",
			LabelColor:  Bold + Cyan,
			RightText:   "[" + tierDisplay + "]",
			RightColor:  Bold + Green,
		},
		{Type: RowSeparator},
		{
			Type:       RowKeyValue,
			Label:      "Script Devs : ",
			LabelColor: Gray,
			Value:      "@NightWitch, @Eysdi",
			ValueColor: White,
		},
		{
			Type:       RowKeyValue,
			Label:      "Clone Credit: ",
			LabelColor: Gray,
			Value:      "@Jep",
			ValueColor: Cyan,
		},
		{
			Type:       RowKeyValue,
			Label:      "Invite Link : ",
			LabelColor: Gray,
			Value:      DiscordInviteURL,
			ValueColor: Cyan,
		},
		{Type: RowSeparator},
		{
			Type:        RowCentered,
			CustomText:  "SESSION PRE-FLIGHT",
			CustomColor: Bold + White,
		},
		{Type: RowSeparator},
	}

	// Detect mixed mode: check if clones have different games assigned
	isMixed := false
	if len(cloneGameConfigs) > 1 {
		for i := 1; i < len(cloneGameConfigs); i++ {
			if cloneGameConfigs[i].Name != cloneGameConfigs[0].Name {
				isMixed = true
				break
			}
		}
	}

	if isMixed {
		rows = append(rows, BoxRow{
			Type:       RowKeyValue,
			Label:      "Experience: ",
			LabelColor: Gray,
			Value:      fmt.Sprintf("Mixed (%d Games)", len(cloneGameConfigs)),
			ValueColor: Amber,
		})
		for i, cfg := range cloneGameConfigs {
			cloneLabel := fmt.Sprintf("  Clone %-2d : ", i+1)
			expType := "Public"
			if strings.Contains(cfg.URL, "share?") || strings.Contains(cfg.URL, "privateServer") || strings.Contains(cfg.Name, "[VIP]") {
				expType = "VIP"
			}
			rows = append(rows, BoxRow{
				Type:       RowKeyValue,
				Label:      cloneLabel,
				LabelColor: Dim,
				Value:      fmt.Sprintf("%s [%s]", cfg.Name, expType),
				ValueColor: White,
			})
		}
	} else {
		displayExpName := gameName
		displayExpURL := gameURL
		if len(cloneGameConfigs) > 0 {
			displayExpName = cloneGameConfigs[0].Name
			displayExpURL = cloneGameConfigs[0].URL
		}
		rows = append(rows, BoxRow{
			Type:       RowKeyValue,
			Label:      "Experience: ",
			LabelColor: Gray,
			Value:      displayExpName,
			ValueColor: White,
		})
		expType := "Public Server"
		typeColor := White
		if strings.Contains(displayExpURL, "share?") || strings.Contains(displayExpURL, "privateServer") || strings.Contains(displayExpName, "[VIP]") {
			expType = "Private Server (VIP)"
			typeColor = Green
		}
		rows = append(rows, BoxRow{
			Type:       RowKeyValue,
			Label:      "Type      : ",
			LabelColor: Gray,
			Value:      expType,
			ValueColor: typeColor,
		})
	}
	rows = append(rows, BoxRow{
		Type:       RowKeyValue,
		Label:      "Instances : ",
		LabelColor: Gray,
		Value:      fmt.Sprintf("%d Clone%s", cloneCount, plural(cloneCount)),
		ValueColor: White,
	})

	rows = append(rows, BoxRow{
		Type:       RowKeyValue,
		Label:      "License   : ",
		LabelColor: Gray,
		Value:      licenseDuration,
		ValueColor: Green,
	})

	sentinelVal := "ACTIVE (Auto-Rejoin)"
	sentinelColor := Green
	if !enableRejoin {
		sentinelVal = "DISABLED (One-time)"
		sentinelColor = Dark
	}
	rows = append(rows, BoxRow{
		Type:       RowStatus,
		Label:      "Sentinel  : ",
		LabelColor: Gray,
		Value:      sentinelVal,
		ValueColor: sentinelColor,
	})

	discordVal := "CONNECTED"
	discordColor := Green
	if discordWebhook == "" {
		discordVal = "DISABLED"
		discordColor = Dark
	}
	rows = append(rows, BoxRow{
		Type:       RowStatus,
		Label:      "Discord   : ",
		LabelColor: Gray,
		Value:      discordVal,
		ValueColor: discordColor,
	})

	optimizerVal := "DEEP CLEAN"
	optimizerColor := Green
	if cleanMode == CleanModeLight {
		optimizerVal = "LIGHT CLEAN"
		optimizerColor = Amber
	} else if cleanMode == CleanModeNone {
		optimizerVal = "DISABLED"
		optimizerColor = Dark
	}
	if cleanedRAMFreedMB > 0 {
		optimizerVal = fmt.Sprintf("%s (+%d MB Freed)", optimizerVal, cleanedRAMFreedMB)
	}
	rows = append(rows, BoxRow{
		Type:       RowStatus,
		Label:      "Optimizer : ",
		LabelColor: Gray,
		Value:      optimizerVal,
		ValueColor: optimizerColor,
	})



	rows = append(rows,
		BoxRow{Type: RowSeparator},
		BoxRow{
			Type:        RowCentered,
			CustomText:  "RESOURCE TELEMETRY",
			CustomColor: Bold + White,
		},
		BoxRow{Type: RowSeparator},
	)

	if res.TotalRAMMB > 0 {
		ramStr := fmt.Sprintf("%.1f/%.1f GB (%.0f%% Used)", res.UsedRAMGB, res.TotalRAMGB, res.RAMUsagePercent)
		rows = append(rows, BoxRow{
			Type:       RowKeyValue,
			Label:      "System RAM: ",
			LabelColor: Gray,
			Value:      ramStr,
			ValueColor: Cyan,
		})
		availStr := fmt.Sprintf("%.1f GB Free / Available", res.AvailableRAMGB)
		rows = append(rows, BoxRow{
			Type:       RowKeyValue,
			Label:      "Avail RAM : ",
			LabelColor: Gray,
			Value:      availStr,
			ValueColor: Green,
		})
	}

	cpuStr := fmt.Sprintf("%.1f%% (%d Cores, %s)", res.CPUUsagePercent, res.CPUCores, res.BitnessDesc)
	rows = append(rows, BoxRow{
		Type:       RowKeyValue,
		Label:      "CPU Load  : ",
		LabelColor: Gray,
		Value:      cpuStr,
		ValueColor: White,
	})

	// Dynamic Per-Instance RAM Telemetry (Live Measured vs Pre-Launch Baseline)
	type cloneMemEntry struct {
		Label string
		Value string
	}
	var actualEntries []cloneMemEntry

	sortedReports := getSortedCloneStatuses()
	for _, rep := range sortedReports {
		if !rep.IsEstimated && rep.RAMMB > 0 {
			var val string
			if rep.Status == "RECOVERING" {
				val = fmt.Sprintf("%d MB (RECOVERING)", rep.RAMMB)
			} else if rep.PID > 0 {
				val = fmt.Sprintf("%d MB (PID %d)", rep.RAMMB, rep.PID)
			} else {
				val = fmt.Sprintf("%d MB RSS", rep.RAMMB)
			}
			cloneTag := fmt.Sprintf("%s RAM: ", rep.DisplayName)
			actualEntries = append(actualEntries, cloneMemEntry{Label: cloneTag, Value: val})
		}
	}

	if len(actualEntries) > 0 {
		for _, ent := range actualEntries {
			rows = append(rows, BoxRow{
				Type:       RowKeyValue,
				Label:      ent.Label,
				LabelColor: Gray,
				Value:      ent.Value,
				ValueColor: Green,
			})
		}
	} else {
		cloneMemStr := fmt.Sprintf("~%d MB / clone (%s)", profile.EstimatedRAMMB, profile.Name)
		rows = append(rows, BoxRow{
			Type:       RowKeyValue,
			Label:      "Memory Est: ",
			LabelColor: Gray,
			Value:      cloneMemStr,
			ValueColor: Amber,
		})
	}

	dashboardMu.Lock()
	stMsg := currentDashboard.Status
	stCol := currentDashboard.StatusColor
	actionStep := currentDashboard.ActionStep
	actionCol := currentDashboard.ActionColor
	queueInfo := currentDashboard.QueueInfo
	hasEv := currentDashboard.HasEvent
	evDesc := currentDashboard.EventDesc
	evTag := currentDashboard.EventTag
	evRAM := currentDashboard.EventRAM
	evTime := currentDashboard.EventTime
	dashboardMu.Unlock()

	if stMsg != "" {
		rows = append(rows,
			BoxRow{Type: RowSeparator},
			BoxRow{
				Type:       RowStatus,
				Label:      "Live Status : ",
				LabelColor: Gray,
				Value:      "● " + stMsg,
				ValueColor: stCol,
			},
		)
	}

	if actionStep != "" {
		if actionCol == "" {
			actionCol = Cyan
		}
		rows = append(rows, BoxRow{
			Type:       RowKeyValue,
			Label:      "Action Step : ",
			LabelColor: Gray,
			Value:      actionStep,
			ValueColor: actionCol,
		})
	}

	if queueInfo != "" {
		rows = append(rows, BoxRow{
			Type:       RowKeyValue,
			Label:      "Crash Queue : ",
			LabelColor: Gray,
			Value:      queueInfo,
			ValueColor: Amber,
		})
	}

	if hasEv {
		evColor := Red
		if evTag == "RECOVERED" || evTag == "RESTORED" {
			evColor = Green
		} else if evTag == "ANR" || evTag == "FREEZE" {
			evColor = Amber
		}

		if evDesc != "" {
			rows = append(rows, BoxRow{
				Type:       RowKeyValue,
				Label:      "Event Alert : ",
				LabelColor: Gray,
				Value:      evDesc,
				ValueColor: evColor,
			})
		}
		if evRAM != "" {
			rows = append(rows, BoxRow{
				Type:       RowKeyValue,
				Label:      "Event Info  : ",
				LabelColor: Gray,
				Value:      evRAM,
				ValueColor: White,
			})
		}
		if evTime != "" {
			rows = append(rows, BoxRow{
				Type:       RowKeyValue,
				Label:      "Event Time  : ",
				LabelColor: Gray,
				Value:      evTime,
				ValueColor: Dim,
			})
		}
	}

	box := renderCenteredBox("SUMMARY", rows, termW, termH, Gray)
	clearTerminal()
	fmt.Print(box)
}

func drawLaunchStatusCard(activeClone, totalClones int, phase, detail string) {
	currentLaunchCard.Lock()
	currentLaunchCard.Active = true
	currentLaunchCard.ActiveClone = activeClone
	currentLaunchCard.TotalClones = totalClones
	currentLaunchCard.Phase = phase
	currentLaunchCard.Detail = detail
	currentLaunchCard.Unlock()

	renderMu.Lock()
	defer renderMu.Unlock()

	termW, termH := detectTerminalSize()
	rows := []BoxRow{
		{
			Type:        RowHeader,
			PrefixIcon:  "◆ ",
			PrefixColor: Cyan,
			Label:       "LAUNCHING INSTANCES",
			LabelColor:  Bold + White,
			RightText:   fmt.Sprintf("%d/%d", activeClone, totalClones),
			RightColor:  Cyan,
		},
		{
			Type:        RowSubtitle,
			CustomText:  "Automated Client Engine & Auto-Join",
			CustomColor: Dim,
		},
		BoxRow{Type: RowSeparator},
		{
			Type:       RowKeyValue,
			Label:      "Target Game : ",
			LabelColor: Gray,
			Value:      truncate(gameName, 24),
			ValueColor: White,
		},
		{
			Type:       RowKeyValue,
			Label:      "Current App : ",
			LabelColor: Gray,
			Value:      fmt.Sprintf("Clone %d of %d", activeClone, totalClones),
			ValueColor: Cyan,
		},
		{
			Type:       RowKeyValue,
			Label:      "Action Step : ",
			LabelColor: Gray,
			Value:      phase,
			ValueColor: Amber,
		},
	}
	if detail != "" {
		rows = append(rows,
			BoxRow{Type: RowSeparator},
			BoxRow{
				Type:        RowSubtitle,
				CustomText:  detail,
				CustomColor: Green,
			},
		)
	}
	box := renderCenteredBox("LAUNCH_STATUS", rows, termW, termH, Gray)
	clearTerminal()
	fmt.Print(box)
}

func drawSentinelActiveCard() {
	currentLaunchCard.Lock()
	currentLaunchCard.Active = false
	currentLaunchCard.Unlock()

	renderMu.Lock()
	defer renderMu.Unlock()

	termW, termH := detectTerminalSize()
	rows := []BoxRow{
		{
			Type:        RowHeader,
			PrefixIcon:  "◆ ",
			PrefixColor: Green,
			Label:       "SENTINEL IN-GAME GUARD",
			LabelColor:  Bold + Green,
			RightText:   "ACTIVE",
			RightColor:  Bold + Green,
		},
		{
			Type:        RowSubtitle,
			CustomText:  "24/7 Crash, ANR & Disconnect Watchdog",
			CustomColor: Dim,
		},
		BoxRow{Type: RowSeparator},
		{
			Type:       RowKeyValue,
			Label:      "Monitored   : ",
			LabelColor: Gray,
			Value:      fmt.Sprintf("%d Clone%s Online", cloneCount, plural(cloneCount)),
			ValueColor: Cyan,
		},
		{
			Type:       RowKeyValue,
			Label:      "Experience  : ",
			LabelColor: Gray,
			Value:      truncate(gameName, 24),
			ValueColor: White,
		},
		{
			Type:       RowKeyValue,
			Label:      "Guard State : ",
			LabelColor: Gray,
			Value:      "● Monitoring 24/7 (Auto-Rejoin)",
			ValueColor: Green,
		},
		BoxRow{Type: RowSeparator},
		{
			Type:        RowSubtitle,
			CustomText:  "All instances successfully launched & synchronized!",
			CustomColor: Green,
		},
		{
			Type:        RowSubtitle,
			CustomText:  "Sentinel will automatically restart clones if they crash.",
			CustomColor: Dim,
		},
	}
	box := renderCenteredBox("SENTINEL_ACTIVE", rows, termW, termH, Green)
	clearTerminal()
	fmt.Print(box)
}

func truncate(s string, maxLen int) string {
	return truncateVisible(s, maxLen)
}

// compareSemver compares two semantic versions (e.g. "1.4.2" vs "1.5.0").
// Returns -1 if v1 < v2, 1 if v1 > v2, 0 if v1 == v2.
func compareSemver(v1, v2 string) int {
	clean := func(s string) []int {
		s = strings.TrimSpace(strings.TrimPrefix(strings.ToLower(s), "v"))
		if idx := strings.IndexAny(s, " |\t\n-"); idx != -1 {
			s = s[:idx]
		}
		parts := strings.Split(s, ".")
		var nums []int
		for _, p := range parts {
			n, _ := strconv.Atoi(strings.TrimSpace(p))
			nums = append(nums, n)
		}
		for len(nums) < 3 {
			nums = append(nums, 0)
		}
		return nums
	}
	p1 := clean(v1)
	p2 := clean(v2)
	for i := 0; i < len(p1) && i < len(p2); i++ {
		if p1[i] < p2[i] {
			return -1
		}
		if p1[i] > p2[i] {
			return 1
		}
	}
	return 0
}

func checkUpdates() {
	var rawBody string
	var reqErr error

	_ = runAnimatedTask("Verifying version & release integrity...", func() error {
		client := &http.Client{Timeout: 5 * time.Second}
		reqURL := fmt.Sprintf("%s?_t=%d", VersionURL, time.Now().Unix())
		resp, err := client.Get(reqURL)
		if err != nil {
			resp, err = client.Get(VersionURL)
		}
		if err != nil {
			reqErr = err
			return err
		}
		defer resp.Body.Close()
		body, _ := io.ReadAll(resp.Body)
		rawBody = strings.TrimSpace(string(body))
		return nil
	})

	latestVersion := ScriptVersion
	releaseDate := ""
	if rawBody != "" {
		lines := strings.Split(rawBody, "\n")
		firstLine := strings.TrimSpace(lines[0])
		if strings.Contains(firstLine, "|") {
			parts := strings.Split(firstLine, "|")
			latestVersion = strings.TrimSpace(parts[0])
			if len(parts) > 1 {
				releaseDate = strings.TrimSpace(parts[1])
			}
		} else {
			latestVersion = firstLine
			if len(lines) > 1 && strings.TrimSpace(lines[1]) != "" {
				releaseDate = strings.TrimSpace(lines[1])
			}
		}
	}

	cmp := compareSemver(ScriptVersion, latestVersion)
	isOutdated := (cmp < 0)

	// Check date if provided in version payload
	isDateExpired := false
	if releaseDate != "" {
		if parsedDate, dErr := time.Parse("2006-01-02", releaseDate); dErr == nil {
			if time.Now().After(parsedDate.Add(24*time.Hour)) && isOutdated {
				isDateExpired = true
			}
		}
	}

	statusText := "VERIFIED (Latest Build)"
	statusColor := Green
	if isOutdated || isDateExpired {
		statusText = "OUTDATED / BLOCKED"
		statusColor = Red
	} else if reqErr != nil {
		statusText = "OFFLINE (Local v" + ScriptVersion + ")"
		statusColor = Amber
	}

	// Also check Delta Executor status dynamically
	latestDelta, lastMod, deltaErr := fetchLatestDeltaVersion()
	installedDelta := getInstalledDeltaVersion()
	displayDelta := getDisplayDeltaVersion()
	isDeltaOld := false
	if deltaErr == nil && latestDelta != "" {
		isDeltaOld = isDeltaOutdated(installedDelta, latestDelta)
		if isDeltaOld {
			deltaUpdateMu.Lock()
			detectedDeltaUpdate = latestDelta
			deltaUpdateNotified = true
			deltaUpdateMu.Unlock()

			writeLog("DELTA_UPDATE", fmt.Sprintf("New Delta: %s (Current: %s)", latestDelta, displayDelta))

			if discordWebhook != "" {
				fields := []DiscordEmbedField{
					{Name: "📱 Current Delta Version", Value: fmt.Sprintf("`%s`", displayDelta), Inline: true},
					{Name: "🚀 New Delta Version", Value: fmt.Sprintf("`%s`", latestDelta), Inline: true},
					{Name: "📅 Release Date", Value: fmt.Sprintf("`%s`", lastMod), Inline: true},
					{Name: "📥 Download Link", Value: fmt.Sprintf("[%s](%s)", DeltaDownloadURL, DeltaDownloadURL), Inline: false},
					{Name: "🕒 Detected At", Value: time.Now().Format("2006-01-02 15:04:05"), Inline: true},
				}
				sendRichWebhook(EventGeneral, "⚠️ Delta Executor Update Detected",
					"A new version of **Delta Executor** has been detected on the official distribution server!\n\nIf your Roblox clones start crashing, freezing, or showing update dialogs, please update your Delta clone APKs.",
					16753920, fields)
			}
		}
	}

	verRows := []BoxRow{
		{
			Type:       RowKeyValue,
			Label:      "Nefarious Hub: ",
			LabelColor: Gray,
			Value:      "v" + ScriptVersion,
			ValueColor: White,
		},
		{
			Type:       RowKeyValue,
			Label:      "Script Status: ",
			LabelColor: Gray,
			Value:      statusText,
			ValueColor: statusColor,
		},
		{Type: RowSeparator},
		{
			Type:       RowKeyValue,
			Label:      "Installed APK: ",
			LabelColor: Gray,
			Value:      displayDelta,
			ValueColor: White,
		},
	}

	if deltaErr == nil && latestDelta != "" {
		verRows = append(verRows, BoxRow{
			Type:       RowKeyValue,
			Label:      "Latest Delta : ",
			LabelColor: Gray,
			Value:      latestDelta,
			ValueColor: White,
		})

		if isDeltaOld {
			verRows = append(verRows,
				BoxRow{
					Type:       RowKeyValue,
					Label:      "Delta Status : ",
					LabelColor: Gray,
					Value:      "UPDATE AVAILABLE",
					ValueColor: Bold + Amber,
				},
				BoxRow{Type: RowSeparator},
				BoxRow{
					Type:        RowSubtitle,
					CustomText:  "• Newer Delta APK available on official server.",
					CustomColor: Dim,
				},
				BoxRow{
					Type:       RowKeyValue,
					Label:      "Download Link: ",
					LabelColor: Gray,
					Value:      DeltaDownloadURL,
					ValueColor: Cyan,
				},
			)
		} else {
			verRows = append(verRows, BoxRow{
				Type:       RowKeyValue,
				Label:      "Delta Status : ",
				LabelColor: Gray,
				Value:      "VERIFIED (Up to Date)",
				ValueColor: Green,
			})
		}
	}

	clearTerminal()
	drawStepCard("SYSTEM VERIFICATION", "Integrity & Client Diagnostics", verRows)
	time.Sleep(2000 * time.Millisecond)

	if isOutdated || isDateExpired {
		writeLog("VERSION", fmt.Sprintf("Installed version v%s is outdated (Required: v%s). Execution halted.", ScriptVersion, latestVersion))
		clearTerminal()
		drawAlertCard("ERROR", "[X] CRITICAL: UPDATE REQUIRED",
			fmt.Sprintf("Installed v%s is lower than required v%s.", ScriptVersion, latestVersion),
			"Launch blocked to prevent ban risks and crashing.",
			"Download latest payload: github.com/relayced/Hexagon")
		fmt.Printf("\n%s[HALTED]%s Update required before continuing. Exiting...\n\n", Red, NC)
		os.Exit(1)
	}

	if reqErr != nil {
		writeLog("VERSION", fmt.Sprintf("Network check skipped (using cached v%s)", ScriptVersion))
	} else {
		writeLog("VERSION", fmt.Sprintf("Version v%s verified and compatible.", ScriptVersion))
	}
}

// ============================================================================
// DELTA EXECUTOR VERSION TRACKING & UPDATE DETECTION
// ============================================================================

type DeltaAPIResponse struct {
	LatestAPK []struct {
		Name         string `json:"name"`
		Size         int64  `json:"size"`
		LastModified string `json:"last_modified"`
		Timestamp    int64  `json:"timestamp"`
	} `json:"latest_apk"`
}

var (
	deltaUpdateNotified = false
	deltaUpdateMu       sync.Mutex
	detectedDeltaUpdate = ""
)

func compareVersions(v1, v2 string) int {
	p1 := strings.Split(v1, ".")
	p2 := strings.Split(v2, ".")
	maxLen := len(p1)
	if len(p2) > maxLen {
		maxLen = len(p2)
	}
	for i := 0; i < maxLen; i++ {
		var n1, n2 int
		if i < len(p1) {
			n1, _ = strconv.Atoi(p1[i])
		}
		if i < len(p2) {
			n2, _ = strconv.Atoi(p2[i])
		}
		if n1 < n2 {
			return -1
		}
		if n1 > n2 {
			return 1
		}
	}
	return 0
}

func isDeltaOutdated(installedVer, latestDelta string) bool {
	if latestDelta == "" {
		return false
	}
	re := regexp.MustCompile(`[0-9]+(\.[0-9]+)+`)
	latestNums := re.FindString(latestDelta)
	if latestNums == "" {
		return false
	}

	if installedVer == "" {
		installedVer = getInstalledDeltaVersion()
	}

	if installedVer != "" {
		installedNums := re.FindString(installedVer)
		if installedNums != "" {
			return compareVersions(installedNums, latestNums) < 0
		}
	}

	return false
}

var (
	cachedInstalledDeltaVersion string
	cachedDeltaVersionMu        sync.Mutex
	lastDeltaVersionCheck       time.Time
)

func extractVersionFromAPK(apkPath string) string {
	r, err := zip.OpenReader(apkPath)
	if err != nil {
		return ""
	}
	defer r.Close()

	for _, f := range r.File {
		if f.Name == "AndroidManifest.xml" {
			rc, err := f.Open()
			if err != nil {
				return ""
			}
			defer rc.Close()
			buf := make([]byte, 16384)
			n, _ := io.ReadFull(rc, buf)
			data := string(buf[:n])
			re := regexp.MustCompile(`([0-9]+\.[0-9]+\.[0-9]+[0-9a-zA-Z._-]*)`)
			if m := re.FindString(data); m != "" {
				return m
			}
			cleanData := strings.ReplaceAll(data, "\x00", "")
			if m := re.FindString(cleanData); m != "" {
				return m
			}
			break
		}
	}
	return ""
}

func getInstalledDeltaVersion() string {
	cachedDeltaVersionMu.Lock()
	if cachedInstalledDeltaVersion != "" && time.Since(lastDeltaVersionCheck) < 3*time.Minute {
		v := cachedInstalledDeltaVersion
		cachedDeltaVersionMu.Unlock()
		return v
	}
	cachedDeltaVersionMu.Unlock()

	var candidates []string
	if len(activePackages) > 0 {
		candidates = append(candidates, activePackages...)
	}
	if len(allPackages) > 0 {
		candidates = append(candidates, allPackages...)
	}
	candidates = append(candidates, "com.roblox.client")

	seen := make(map[string]bool)
	var uniqueCandidates []string
	for _, pkg := range candidates {
		if !seen[pkg] {
			seen[pkg] = true
			uniqueCandidates = append(uniqueCandidates, pkg)
		}
	}

	versionRegex := regexp.MustCompile(`versionName=["']?([0-9a-zA-Z._-]+)["']?`)

	for _, pkg := range uniqueCandidates {
		// 1. Try dumpsys package, cmd package dump, and pm dump
		dumpCmds := []string{
			fmt.Sprintf("dumpsys package %s 2>/dev/null", pkg),
			fmt.Sprintf("cmd package dump %s 2>/dev/null", pkg),
			fmt.Sprintf("pm dump %s 2>/dev/null", pkg),
		}
		if checkRoot() {
			dumpCmds = append([]string{
				fmt.Sprintf("su -c 'dumpsys package %s' 2>/dev/null", pkg),
				fmt.Sprintf("su -c 'cmd package dump %s' 2>/dev/null", pkg),
				fmt.Sprintf("su -c 'pm dump %s' 2>/dev/null", pkg),
			}, dumpCmds...)
		}

		for _, cmdStr := range dumpCmds {
			out, err := exec.Command("sh", "-c", cmdStr).Output()
			if err == nil && len(out) > 0 {
				if m := versionRegex.FindStringSubmatch(string(out)); len(m) > 1 {
					found := strings.TrimSpace(m[1])
					if found != "" {
						cachedDeltaVersionMu.Lock()
						cachedInstalledDeltaVersion = found
						lastDeltaVersionCheck = time.Now()
						cachedDeltaVersionMu.Unlock()
						return found
					}
				}
			}
		}

		// 2. Fallback: try pm path to inspect APK
		pathCmds := []string{
			fmt.Sprintf("pm path %s 2>/dev/null", pkg),
		}
		if checkRoot() {
			pathCmds = append([]string{fmt.Sprintf("su -c 'pm path %s' 2>/dev/null", pkg)}, pathCmds...)
		}
		for _, pCmd := range pathCmds {
			out, err := exec.Command("sh", "-c", pCmd).Output()
			if err == nil && len(out) > 0 {
				lines := strings.Split(string(out), "\n")
				for _, l := range lines {
					l = strings.TrimSpace(l)
					if strings.HasPrefix(l, "package:") {
						apkPath := strings.TrimPrefix(l, "package:")
						if ver := extractVersionFromAPK(apkPath); ver != "" {
							cachedDeltaVersionMu.Lock()
							cachedInstalledDeltaVersion = ver
							lastDeltaVersionCheck = time.Now()
							cachedDeltaVersionMu.Unlock()
							return ver
						}
					}
				}
			}
		}
	}

	return ""
}

func getDisplayDeltaVersion() string {
	ver := getInstalledDeltaVersion()
	if ver == "" {
		return "Not Installed / Unknown"
	}
	if strings.HasPrefix(strings.ToLower(ver), "delta-") {
		return ver
	}
	return "Delta-" + ver
}

func checkForUpgradeDialog() bool {
	cmds := []string{
		"dumpsys window windows 2>/dev/null",
		"dumpsys activity top 2>/dev/null",
		"dumpsys window visible-apps 2>/dev/null",
		"logcat -d -t 150 2>/dev/null",
	}
	if checkRoot() {
		cmds = append(cmds, "su -c 'dumpsys window windows' 2>/dev/null")
		cmds = append(cmds, "su -c 'logcat -d -t 150' 2>/dev/null")
	}
	for _, cmdStr := range cmds {
		out, err := exec.Command("sh", "-c", cmdStr).Output()
		if err == nil && len(out) > 0 {
			s := string(out)
			if strings.Contains(s, "Roblox Upgrade") ||
				strings.Contains(s, "out of date and will not work") ||
				strings.Contains(s, "Taking you to the Google Play Store") ||
				(strings.Contains(s, "UpgradeDialog") && strings.Contains(strings.ToLower(s), "roblox")) {
				return true
			}
		}
	}
	return false
}

func isDeltaUpdateAvailable() bool {
	deltaUpdateMu.Lock()
	if detectedDeltaUpdate != "" {
		deltaUpdateMu.Unlock()
		return true
	}
	deltaUpdateMu.Unlock()

	latestName, _, err := fetchLatestDeltaVersion()
	if err == nil && latestName != "" {
		installedVer := getInstalledDeltaVersion()
		if isDeltaOutdated(installedVer, latestName) {
			deltaUpdateMu.Lock()
			detectedDeltaUpdate = latestName
			deltaUpdateMu.Unlock()
			return true
		}
	}
	return false
}

func handleDeltaUpgradeAbort(reason string, pkgsToStop []string) {
	deltaUpdateMu.Lock()
	ver := detectedDeltaUpdate
	deltaUpdateMu.Unlock()
	if ver == "" {
		latestName, _, err := fetchLatestDeltaVersion()
		if err == nil && latestName != "" {
			ver = latestName
		} else {
			ver = "Latest Delta Available"
		}
	}

	installedVer := getDisplayDeltaVersion()

	writeLog("DELTA_UPGRADE_ABORT", fmt.Sprintf("Joining stopped: %s (Installed: %s, Reason: %s)", ver, installedVer, reason))

	stopList := pkgsToStop
	if len(stopList) == 0 {
		stopList = activePackages
	}
	for _, pkg := range stopList {
		if checkRoot() {
			_ = exec.Command("su", "-c", "am force-stop "+pkg).Run()
		} else {
			_ = exec.Command("am", "force-stop", pkg).Run()
		}
	}

	if discordWebhook != "" {
		fields := []DiscordEmbedField{
			{Name: "🛑 Action", Value: "`Joining Stopped Immediately`", Inline: true},
			{Name: "📱 Current Client", Value: fmt.Sprintf("`%s`", installedVer), Inline: true},
			{Name: "🚀 Required Delta", Value: fmt.Sprintf("`%s`", ver), Inline: true},
			{Name: "📥 Download Link", Value: fmt.Sprintf("[%s](%s)", DeltaDownloadURL, DeltaDownloadURL), Inline: false},
			{Name: "🕒 Stopped At", Value: time.Now().Format("2006-01-02 15:04:05"), Inline: true},
		}
		sendRichWebhook(EventGeneral, "🛑 Joining Aborted: Delta Upgrade Required",
			"Roblox has forced a client upgrade. The joining process of all clones was **immediately stopped** because outdated clients cannot connect to games.\n\nPlease download and install the new Delta clone APKs.",
			15158332, fields)
	}

	clearTerminal()
	termW, termH := detectTerminalSize()

	rows := []BoxRow{
		{
			Type:        RowCentered,
			CustomText:  "[!] DELTA UPGRADE REQUIRED - JOINING STOPPED",
			CustomColor: Bold + Red,
		},
		{Type: RowSeparator},
		{
			Type:       RowKeyValue,
			Label:      "Latest Delta : ",
			LabelColor: Gray,
			Value:      ver,
			ValueColor: Bold + White,
		},
		{
			Type:       RowKeyValue,
			Label:      "Installed APK: ",
			LabelColor: Gray,
			Value:      installedVer + " (Outdated)",
			ValueColor: Bold + Amber,
		},
		{
			Type:       RowKeyValue,
			Label:      "Trigger      : ",
			LabelColor: Gray,
			Value:      reason,
			ValueColor: Red,
		},
		{Type: RowSeparator},
		{
			Type:        RowSubtitle,
			CustomText:  "• Roblox has forced an upgrade; outdated clients cannot join.",
			CustomColor: Dim,
		},
		{
			Type:        RowSubtitle,
			CustomText:  "• Please update your Delta clone APKs before running.",
			CustomColor: White,
		},
		{
			Type:       RowKeyValue,
			Label:      "Download APK : ",
			LabelColor: Gray,
			Value:      DeltaDownloadURL,
			ValueColor: Cyan,
		},
	}

	box := renderCenteredBox("ALERT", rows, termW, termH, Red)
	fmt.Print(box)

	pad := getMenuLeftPad()
	fmt.Printf("\n%s%s[!] Joining halted. Update your Delta clones and rerun Nefarious.%s\n\n", pad, Bold+Red, NC)
}

func fetchLatestDeltaVersion() (string, string, error) {
	tr := &http.Transport{
		TLSClientConfig: &tls.Config{InsecureSkipVerify: true},
	}
	client := &http.Client{Transport: tr, Timeout: 8 * time.Second}
	req, err := http.NewRequest("GET", DeltaAPIURL, nil)
	var bodyBytes []byte
	if err == nil {
		req.Header.Set("User-Agent", "Mozilla/5.0 (Linux; Android 10; K) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Mobile Safari/537.36")
		req.Header.Set("Accept", "application/json")
		resp, err := client.Do(req)
		if err == nil && resp != nil {
			defer resp.Body.Close()
			if resp.StatusCode == 200 {
				bodyBytes, _ = io.ReadAll(resp.Body)
			}
		}
	}

	if len(bodyBytes) == 0 {
		cmd := exec.Command("curl", "-s", "-A", "Mozilla/5.0 (Linux; Android 10; K) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Mobile Safari/537.36", DeltaAPIURL)
		out, cErr := cmd.Output()
		if cErr == nil && len(out) > 0 {
			bodyBytes = out
		}
	}

	if len(bodyBytes) == 0 {
		return "", "", fmt.Errorf("failed to reach Delta API")
	}

	var res DeltaAPIResponse
	if err := json.Unmarshal(bodyBytes, &res); err != nil {
		return "", "", err
	}

	if len(res.LatestAPK) == 0 || res.LatestAPK[0].Name == "" {
		return "", "", fmt.Errorf("no Delta APK found in response")
	}

	rawName := res.LatestAPK[0].Name
	cleanName := strings.TrimSuffix(rawName, ".apk")
	return cleanName, res.LatestAPK[0].LastModified, nil
}

func checkDeltaUpdate(isStartup bool) {
	if isStartup {
		return
	}
	latestName, lastMod, err := fetchLatestDeltaVersion()
	if err != nil {
		return
	}

	installedVer := getInstalledDeltaVersion()
	displayVer := getDisplayDeltaVersion()
	if isDeltaOutdated(installedVer, latestName) {
		deltaUpdateMu.Lock()
		alreadyNotified := deltaUpdateNotified
		deltaUpdateNotified = true
		detectedDeltaUpdate = latestName
		deltaUpdateMu.Unlock()

		if !alreadyNotified {
			currTime := time.Now().Format("15:04:05")
			writeLog("DELTA_UPDATE", fmt.Sprintf("New Delta: %s (Current: %s)", latestName, displayVer))
			setDashboardEvent("Delta Update: "+latestName, Amber, "UPDATE", "New: "+latestName, "", currTime)

			// Dispatch alert to Discord Webhook
			fields := []DiscordEmbedField{
				{Name: "📱 Current Delta Version", Value: fmt.Sprintf("`%s`", displayVer), Inline: true},
				{Name: "🚀 New Delta Version", Value: fmt.Sprintf("`%s`", latestName), Inline: true},
				{Name: "📅 Release Date", Value: fmt.Sprintf("`%s`", lastMod), Inline: true},
				{Name: "📥 Download Link", Value: fmt.Sprintf("[%s](%s)", DeltaDownloadURL, DeltaDownloadURL), Inline: false},
				{Name: "🕒 Detected At", Value: time.Now().Format("2006-01-02 15:04:05"), Inline: true},
			}
			sendRichWebhook(EventGeneral, "⚠️ Delta Executor Update Detected",
				fmt.Sprintf("A new version of **Delta Executor** has been detected on the official distribution server!\n\nIf your Roblox clones start crashing, freezing, or showing update dialogs, please update your Delta clone APKs."),
				16753920, fields)
		}
	}
}

func startDeltaUpdatePoller() {
	ticker := time.NewTicker(20 * time.Minute)
	go func() {
		for range ticker.C {
			checkDeltaUpdate(false)
		}
	}()
}

// ============================================================================
// LICENSE CONFIGURATION
// ============================================================================

func verifyLicense() {
	licenseKey = "Free"
	licenseDuration = "Free"
	isUniversalKey = false
	serverPlaceID = "107778070777162"
	serverGameName = "Steal An Egg"
}

// ============================================================================
// CONFIGURATION MENUS
// ============================================================================

func configureConcurrency() {
	drainInput()
	res := getSystemResources()
	rec := getRecommendedClones(res)

	for {
		pad := getMenuLeftPad()
		var rows []BoxRow
		rows = append(rows,
			BoxRow{
				Type:        RowSubtitle,
				CustomText:  "Runs multiple Roblox accounts at once to farm.",
				CustomColor: White,
			},
			BoxRow{
				Type:        RowSubtitle,
				CustomText:  "Each clone uses ~650-800MB RAM.",
				CustomColor: Dim,
			},
			BoxRow{Type: RowSeparator},
		)

		for i := 1; i <= 6; i++ {
			var note string
			var color string = White
			if i == rec {
				note = "★ Recommended (CPU & RAM Balanced)"
				color = Green
			} else if i == 1 {
				note = "Solo - Lightest Load"
				color = Dim
			} else if i < rec {
				note = "Safe & Lightweight"
				color = Dim
			} else if i-rec == 1 {
				note = "Moderate Hardware Pressure"
				color = Amber
			} else if i-rec == 2 {
				note = "High Risk of Crash / OOM"
				color = Amber
				if res.CPUCores <= 4 && i > 2 {
					note = fmt.Sprintf("High CPU Overload (Capped by %d Cores)", res.CPUCores)
					color = Red
				}
			} else {
				note = "Extreme CPU & RAM Pressure"
				color = Red
				if res.CPUCores <= 4 && i > 2 {
					note = fmt.Sprintf("High CPU Overload (Capped by %d Cores)", res.CPUCores)
				}
			}
			rows = append(rows, BoxRow{
				Type:       RowKeyValue,
				Label:      fmt.Sprintf("[%d] %d Clone%s  ", i, i, plural(i)),
				LabelColor: color,
				Value:      note,
				ValueColor: color,
			})
		}

		rows = append(rows,
			BoxRow{Type: RowSeparator},
			BoxRow{
				Type:        RowSubtitle,
				CustomText:  fmt.Sprintf("Tip: Press [ENTER] to use recommended (%d Clones)", rec),
				CustomColor: Green,
			},
		)

		sub := "Select number of Roblox clones to run"
		if res.TotalRAMMB > 0 {
			sub = fmt.Sprintf("RAM: %.1fGB | CPU: %d Cores (%s, %.0f%%) | Rec: %d Clones", res.TotalRAMGB, res.CPUCores, res.BitnessDesc, res.CPUUsagePercent, rec)
		}
		drawStepCard("1. INSTANCE CONCURRENCY", sub, rows)

		fmt.Printf("%s› Clones [1-6] (default: %d): %s", pad+White, rec, NC)
		input := strings.TrimSpace(readLine())
		selected := rec
		if input != "" {
			c, err := strconv.Atoi(input)
			if err != nil || c < 1 || c > 6 {
				drawAlertCard("ERROR", "[!] INVALID ENTRY", "Please enter a number between 1 and 6.", "", "")
				time.Sleep(1500 * time.Millisecond)
				continue
			}
			selected = c
		}

		if selected > rec {
			warnText := fmt.Sprintf("%d clones exceeds recommendation (%d).", selected, rec)
			if res.CPUCores <= 4 && selected > 2 {
				warnText = fmt.Sprintf("%d clones will heavily overload your %d-Core CPU!", selected, res.CPUCores)
			}
			warnRows := []BoxRow{
				{Type: RowSubtitle, CustomText: warnText, CustomColor: Amber},
				{Type: RowSubtitle, CustomText: "May cause high thermal throttling, ANR freezes & crashing.", CustomColor: Red},
				{Type: RowSeparator},
				{Type: RowSubtitle, CustomText: "Proceed anyway? [y/N] (default: N)", CustomColor: White},
			}
			drawStepCard("HARDWARE WARNING", "CPU & Memory Overload Warning", warnRows)
			fmt.Printf("%s› Proceed with %d clones? [y/N]: %s", pad+White, selected, NC)
			conf := strings.ToLower(strings.TrimSpace(readLine()))
			if conf != "y" && conf != "yes" {
				continue
			}
		}

		// Verify installed packages
		missing, ok := checkInstalledClones(selected)
		if !ok {
			termW, termH := detectTerminalSize()
			missingRows := []BoxRow{
				{Type: RowCentered, CustomText: "[!] CLONE APP NOT INSTALLED", CustomColor: Bold + Red},
				{Type: RowSeparator},
				{Type: RowSubtitle, CustomText: "The following clone app(s) are not", CustomColor: Red},
				{Type: RowSubtitle, CustomText: "installed on this device:", CustomColor: Red},
			}
			for _, m := range missing {
				missingRows = append(missingRows, BoxRow{
					Type: RowSubtitle, CustomText: "  • " + m, CustomColor: Amber,
				})
			}
			missingRows = append(missingRows, BoxRow{Type: RowBlank})
			missingRows = append(missingRows, BoxRow{Type: RowSubtitle, CustomText: "Cannot proceed. Please install the", CustomColor: White})
			if selected > 1 {
				missingRows = append(missingRows, BoxRow{Type: RowSubtitle, CustomText: "missing APK(s) or select fewer clones.", CustomColor: Red})
			} else {
				missingRows = append(missingRows, BoxRow{Type: RowSubtitle, CustomText: "missing APK before running Nefarious.", CustomColor: Red})
			}
			fmt.Print(renderCenteredBox("MISSING_CLONES", missingRows, termW, termH, Red))
			fmt.Printf("\n%s%sPress [ENTER] to choose another clone count...%s", pad, White, NC)
			readLine()
			continue
		}

		cloneCount = selected
		activePackages = allPackages[:cloneCount]
		setDashboardStatus(fmt.Sprintf("%d Clones Selected", cloneCount), Green)
		break
	}
}

// pickOneGame presents the standard game picker and returns a filled CloneGameConfig.
// If initialChoice is provided (e.g. "1", "2", "3"), it skips the selection card and enters that flow directly.
// Returns ok=false if the user chose 'back' from a sub-menu.
func pickOneGame(title string, initialChoice ...string) (cfg CloneGameConfig, ok bool) {
	pad := getMenuLeftPad()
	firstRun := true
	var preChoice string
	if len(initialChoice) > 0 {
		preChoice = strings.TrimSpace(initialChoice[0])
	}

	for {
		choice := ""
		if firstRun && preChoice != "" {
			choice = preChoice
			firstRun = false
		} else {
			firstRun = false
			drainInput()
			rows := []BoxRow{
				{Type: RowSubtitle, CustomText: "Select the game to farm in.", CustomColor: White},
				{Type: RowSubtitle, CustomText: "Sentinel will keep the account connected 24/7.", CustomColor: Dim},
				BoxRow{Type: RowSeparator},
				{Type: RowKeyValue, Label: "[1] Steal An Egg ", LabelColor: Green, Value: "Public Server (Default)", ValueColor: Green},
				{Type: RowKeyValue, Label: "[2] Custom Game  ", LabelColor: White, Value: "Paste Game Link / Place ID", ValueColor: Dim},
				{Type: RowKeyValue, Label: "[3] Private VIP  ", LabelColor: White, Value: "Private Server Share Link", ValueColor: Dim},
				BoxRow{Type: RowSeparator},
				{Type: RowSubtitle, CustomText: "Tip: [ENTER] = Steal An Egg | type 'back' to go back", CustomColor: Green},
			}
			drawStepCard(title, "Roblox Auto-Join & Farm Target", rows)
			fmt.Printf("%s> Selection [1-3] ('back' to cancel): %s", pad+White, NC)
			choice = strings.TrimSpace(readLine())

			// Allow cancelling back to the parent menu (e.g. from Mixed mode clone loop)
			if strings.ToLower(choice) == "back" {
				return CloneGameConfig{}, false
			}
		}

		switch {
		case choice == "" || choice == "1":
			pid := serverPlaceID
			if pid == "" {
				pid = "107778070777162"
			}
			name := serverGameName
			if name == "" {
				name = "Steal An Egg"
			}
			return CloneGameConfig{URL: "roblox://placeId=" + pid, Name: name}, true

		case choice == "2":
			for {
				drawStepCard("CUSTOM EXPERIENCE", "Enter Place ID or Game URL", []BoxRow{
					{Type: RowSubtitle, CustomText: "Paste your Roblox game URL or Place ID.", CustomColor: White},
					{Type: RowSubtitle, CustomText: "Example: roblox.com/games/107778070777162", CustomColor: Dim},
					{Type: RowSeparator},
					{Type: RowSubtitle, CustomText: "Type 'back' to return to menu.", CustomColor: Cyan},
				})
				fmt.Printf("%s> URL / Place ID: %s", pad+White, NC)
				link := strings.TrimSpace(readLine())
				if strings.ToLower(link) == "back" {
					break
				}
				customID := ""
				rePlace := regexp.MustCompile(`[?&]placeId=([0-9]+)`)
				if m := rePlace.FindStringSubmatch(link); len(m) > 1 {
					customID = m[1]
				}
				if customID == "" {
					reGames := regexp.MustCompile(`/games/([0-9]+)`)
					if m := reGames.FindStringSubmatch(link); len(m) > 1 {
						customID = m[1]
					}
				}
				if customID == "" && regexp.MustCompile(`^[0-9]+$`).MatchString(link) {
					customID = link
				}
				if customID == "" {
					drawAlertCard("ERROR", "[!] INVALID GAME ID", "Could not detect Place ID.", "Enter a valid game URL or numeric ID.", "")
					time.Sleep(1500 * time.Millisecond)
					continue
				}
				cName := ""
				reName := regexp.MustCompile(`/games/[0-9]+/([^/?]*)`)
				if m := reName.FindStringSubmatch(link); len(m) > 1 && m[1] != "" {
					cleanSlug := strings.ReplaceAll(m[1], "-", " ")
					cleanSlug = strings.ReplaceAll(cleanSlug, "_", " ")
					words := strings.Fields(cleanSlug)
					for idx, w := range words {
						if len(w) > 0 {
							words[idx] = strings.ToUpper(w[:1]) + w[1:]
						}
					}
					cName = strings.Join(words, " ")
				}
				if cName == "" {
					drawStepCard("EXPERIENCE NAME", "Display Name for Dashboard", []BoxRow{
						{Type: RowSubtitle, CustomText: "Enter a friendly name for this game.", CustomColor: White},
						{Type: RowSubtitle, CustomText: "Example: Blox Fruits or Fisch", CustomColor: Dim},
						{Type: RowSeparator},
						{Type: RowSubtitle, CustomText: "Press [ENTER] for default naming.", CustomColor: Cyan},
					})
					fmt.Printf("%s> Game Name: %s", pad+White, NC)
					nameInput := strings.TrimSpace(readLine())
					if nameInput != "" {
						cName = nameInput
					} else {
						cName = "Custom Experience (" + customID + ")"
					}
				}
				return CloneGameConfig{URL: "roblox://placeId=" + customID, Name: cName}, true
			}

		case choice == "3":
			for {
				drawStepCard("PRIVATE VIP SERVER", "Private Server Share Link", []BoxRow{
					{Type: RowSubtitle, CustomText: "Paste your private server share link.", CustomColor: White},
					{Type: RowSubtitle, CustomText: "Example: roblox.com/share?code=...&type=Server", CustomColor: Dim},
					{Type: RowSeparator},
					{Type: RowSubtitle, CustomText: "Type 'back' to return to menu.", CustomColor: Cyan},
				})
				fmt.Printf("%s> Private Server URL: %s", pad+White, NC)
				link := strings.TrimSpace(readLine())
				if strings.ToLower(link) == "back" {
					break
				}
				if !strings.Contains(link, "roblox.com") && !strings.Contains(link, "roblox://") {
					drawAlertCard("ERROR", "[!] INVALID VIP LINK", "Must be a valid Roblox share link.", "", "")
					time.Sleep(1500 * time.Millisecond)
					continue
				}
				drawStepCard("VIP SERVER NAME", "Display Name for Dashboard", []BoxRow{
					{Type: RowSubtitle, CustomText: "Enter a display name for this VIP server.", CustomColor: White},
					{Type: RowSubtitle, CustomText: "Example: Steal An Egg [VIP]", CustomColor: Dim},
				})
				fmt.Printf("%s> VIP Server Name: %s", pad+White, NC)
				nameInput := strings.TrimSpace(readLine())
				if nameInput == "" {
					nameInput = "Private Server Experience"
				}
				if !strings.Contains(nameInput, "[VIP]") {
					nameInput += " [VIP]"
				}
				return CloneGameConfig{URL: link, Name: nameInput}, true
			}

		default:
			drawAlertCard("ERROR", "[!] INVALID CHOICE", "Please enter 1, 2, or 3.", "", "")
			time.Sleep(1500 * time.Millisecond)
		}
	}
}

func configureTargetExperience() {
	pad := getMenuLeftPad()
	for {
		rows := []BoxRow{
			{Type: RowSubtitle, CustomText: "Select the game your clones will farm in.", CustomColor: White},
			{Type: RowSubtitle, CustomText: "Sentinel will keep accounts connected 24/7.", CustomColor: Dim},
			BoxRow{Type: RowSeparator},
			{Type: RowKeyValue, Label: "[1] Steal An Egg ", LabelColor: Green, Value: "Public Server (Default)", ValueColor: Green},
			{Type: RowKeyValue, Label: "[2] Custom Game  ", LabelColor: White, Value: "Paste Game Link / Place ID", ValueColor: Dim},
			{Type: RowKeyValue, Label: "[3] Private VIP  ", LabelColor: White, Value: "Private Server Share Link", ValueColor: Dim},
		}
		if cloneCount > 1 {
			rows = append(rows, BoxRow{
				Type: RowKeyValue, Label: "[4] Mixed Mode  ", LabelColor: Amber,
				Value: fmt.Sprintf("Assign a different game to each of your %d clones", cloneCount), ValueColor: Amber,
			})
		}
		tip := "Tip: Press [ENTER] to farm Steal An Egg (Default)"
		if cloneCount > 1 {
			tip = "Tip: Use [4] Mixed Mode to run different games across clones"
		}
		rows = append(rows, BoxRow{Type: RowSeparator}, BoxRow{Type: RowSubtitle, CustomText: tip, CustomColor: Green})
		drawStepCard("2. TARGET EXPERIENCE", "Roblox Auto-Join & Farm Target", rows)

		prompt := "> Selection [1-3] (default: 1): "
		if cloneCount > 1 {
			prompt = "> Selection [1-4] (default: 1): "
		}
		fmt.Printf("%s%s%s", pad+White, prompt, NC)
		choice := strings.TrimSpace(readLine())

		// [4] MIXED MODE - assign a different game to each clone
		if choice == "4" {
			if cloneCount <= 1 {
				drawAlertCard("ERROR", "[!] MIXED MODE UNAVAILABLE", "Mixed mode requires 2 or more clones.", "", "")
				time.Sleep(1500 * time.Millisecond)
				continue
			}
			configs := make([]CloneGameConfig, 0, cloneCount)
			cancelled := false
			for i := 0; i < cloneCount; i++ {
				cloneLabel := fmt.Sprintf("2. GAME - CLONE %d of %d", i+1, cloneCount)
				cfg, ok := pickOneGame(cloneLabel)
				if !ok {
					cancelled = true
					break
				}
				configs = append(configs, cfg)
			}
			if cancelled {
				continue
			}
			cloneGameConfigs = configs
			gameURL = configs[0].URL
			gameName = configs[0].Name
			break
		}

		// Single-game paths (1 / 2 / 3 / blank) - delegate to pickOneGame
		if choice != "" && choice != "1" && choice != "2" && choice != "3" {
			drawAlertCard("ERROR", "[!] INVALID CHOICE", fmt.Sprintf("Please enter a number between 1 and %d.", map[bool]int{true: 4, false: 3}[cloneCount > 1]), "", "")
			time.Sleep(1500 * time.Millisecond)
			continue
		}
		if choice == "" {
			choice = "1"
		}
		cfg, ok := pickOneGame("2. TARGET EXPERIENCE", choice)
		if !ok {
			continue
		}
		cloneGameConfigs = make([]CloneGameConfig, cloneCount)
		for i := range cloneGameConfigs {
			cloneGameConfigs[i] = cfg
		}
		gameURL = cfg.URL
		gameName = cfg.Name
		break
	}
}

func configureSentinel() {
	pad := getMenuLeftPad()
	rows := []BoxRow{
		{
			Type:        RowSubtitle,
			CustomText:  "Sentinel is your 24/7 background guard.",
			CustomColor: White,
		},
		{
			Type:        RowSubtitle,
			CustomText:  "• Auto-rejoins if disconnected or kicked (273/277)",
			CustomColor: Cyan,
		},
		{
			Type:        RowSubtitle,
			CustomText:  "• Auto-restarts frozen or crashed clones",
			CustomColor: Cyan,
		},
		{
			Type:        RowSubtitle,
			CustomText:  "• Keeps your accounts farming without manual fix",
			CustomColor: Cyan,
		},
		BoxRow{Type: RowSeparator},
		{
			Type:        RowSubtitle,
			CustomText:  "Recommended: Keep Enabled (Press ENTER for Yes)",
			CustomColor: Green,
		},
	}
	drawStepCard("3. SENTINEL IN-GAME GUARD", "Automated 24/7 Watchdog & Auto-Rejoin", rows)

	fmt.Printf("%s› Enable Sentinel monitor? [Y/n] (default: Y): %s", pad+White, NC)

	for {
		choice := strings.ToLower(strings.TrimSpace(readLine()))
		if choice == "" || choice == "y" || choice == "yes" {
			enableRejoin = true
			break
		} else if choice == "n" || choice == "no" {
			enableRejoin = false
			break
		}
		fmt.Printf("%s%sPlease enter Y or N: %s", pad, Red, NC)
	}

}

func configureWebhook() {
	webhookCache := filepath.Join(getHomeDir(), ".nefhub_webhook")
	cachedWebhook := ""
	if data, err := os.ReadFile(webhookCache); err == nil {
		cachedWebhook = strings.TrimSpace(string(data))
	}
	discordMention = loadDiscordMention()

	pad := getMenuLeftPad()
	var rows []BoxRow

	validateURL := func(u string) bool {
		return strings.HasPrefix(u, "https://discord.com/api/webhooks/") ||
			strings.HasPrefix(u, "https://discordapp.com/api/webhooks/")
	}

	if cachedWebhook != "" {
		rows = append(rows,
			BoxRow{
				Type:        RowSubtitle,
				CustomText:  "Sends live crash, freeze & recovery alerts.",
				CustomColor: White,
			},
			BoxRow{Type: RowSeparator},
			BoxRow{
				Type:       RowKeyValue,
				Label:      "Saved : ",
				LabelColor: Gray,
				Value:      truncate(cachedWebhook, 32),
				ValueColor: Cyan,
			},
		)
		if discordMention != "" {
			rows = append(rows, BoxRow{
				Type:       RowKeyValue,
				Label:      "Ping  : ",
				LabelColor: Gray,
				Value:      discordMention,
				ValueColor: Cyan,
			})
		} else {
			rows = append(rows, BoxRow{
				Type:       RowKeyValue,
				Label:      "Ping  : ",
				LabelColor: Gray,
				Value:      "Disabled (No User ID)",
				ValueColor: Dim,
			})
		}
		rows = append(rows,
			BoxRow{Type: RowSeparator},
			BoxRow{
				Type:        RowSubtitle,
				CustomText:  "• Press [ENTER] to use saved webhook",
				CustomColor: Green,
			},
			BoxRow{
				Type:        RowSubtitle,
				CustomText:  "• Type 'none' to disable Discord alerts",
				CustomColor: Dim,
			},
			BoxRow{
				Type:        RowSubtitle,
				CustomText:  "• Or paste a new Discord Webhook URL",
				CustomColor: Dim,
			},
		)
		drawStepCard("4. DISCORD NOTIFICATIONS", "Live alerts & crash reports", rows)

		fmt.Printf("%s› Action (default: keep saved): %s", pad+White, NC)
		input := strings.TrimSpace(readLine())

		if input == "" {
			discordWebhook = cachedWebhook
			sendWebhook("Sentinel Connected", "Discord alerts verified. Real-time crash, freeze & recovery alerts active.", 3066993)
		} else if strings.ToLower(input) == "none" || strings.ToLower(input) == "no" {
			discordWebhook = ""
			_ = os.Remove(webhookCache)
			saveDiscordMention("")
			return
		} else {
			for {
				if validateURL(input) {
					discordWebhook = input
					_ = os.WriteFile(webhookCache, []byte(discordWebhook), 0600)
					sendWebhook("Sentinel Connected", "Discord alerts verified. Real-time crash, freeze & recovery alerts active.", 3066993)
					break
				}
				drawAlertCard("ERROR", "[!] INVALID WEBHOOK URL", "Must start with https://discord.com/api/webhooks/", "", "")
				fmt.Printf("%s› Webhook URL: %s", pad+White, NC)
				input = strings.TrimSpace(readLine())
			}
		}
	} else {
		rows = append(rows,
			BoxRow{
				Type:        RowSubtitle,
				CustomText:  "Sends real-time alerts to your Discord channel.",
				CustomColor: White,
			},
			BoxRow{
				Type:        RowSubtitle,
				CustomText:  "Optional! You can safely skip if not using Discord.",
				CustomColor: Dim,
			},
			BoxRow{Type: RowSeparator},
			BoxRow{
				Type:        RowSubtitle,
				CustomText:  "• [Y] Set up a Discord Webhook URL",
				CustomColor: White,
			},
			BoxRow{
				Type:        RowSubtitle,
				CustomText:  "• [N] Skip Discord alerts (Press ENTER)",
				CustomColor: Green,
			},
		)
		drawStepCard("4. DISCORD NOTIFICATIONS", "Live alerts & crash reports", rows)

		fmt.Printf("%s› Configure Discord webhook? [y/N] (default: N): %s", pad+White, NC)
		choice := strings.ToLower(strings.TrimSpace(readLine()))
		if choice == "y" || choice == "yes" {
			drawStepCard("DISCORD WEBHOOK URL", "Paste Webhook URL from Discord Channel", []BoxRow{
				{Type: RowSubtitle, CustomText: "In Discord: Channel Settings > Integrations", CustomColor: White},
				{Type: RowSubtitle, CustomText: "> Webhooks > New Webhook > Copy Webhook URL.", CustomColor: Dim},
			})
			for {
				fmt.Printf("%s› Webhook URL: %s", pad+White, NC)
				input := strings.TrimSpace(readLine())
				if validateURL(input) {
					discordWebhook = input
					_ = os.WriteFile(webhookCache, []byte(discordWebhook), 0600)
					sendWebhook("Sentinel Connected", "Discord alerts verified. Real-time crash, freeze & recovery alerts active.", 3066993)
					break
				}
				drawAlertCard("ERROR", "[!] INVALID WEBHOOK URL", "Must start with https://discord.com/api/webhooks/", "", "")
			}
		} else {
			discordWebhook = ""
			return
		}
	}

	// Configure user mention option inside its own step card!
	if discordWebhook != "" {
		currentPingDesc := "None (Skipped)"
		if discordMention != "" {
			currentPingDesc = discordMention
		}
		drawStepCard("DISCORD USER PING", "Optional Crash & Freeze Mentions", []BoxRow{
			{
				Type:        RowSubtitle,
				CustomText:  "Get tagged in Discord when an account crashes.",
				CustomColor: White,
			},
			BoxRow{Type: RowSeparator},
			{
				Type:       RowKeyValue,
				Label:      "Current : ",
				LabelColor: Gray,
				Value:      currentPingDesc,
				ValueColor: Cyan,
			},
			BoxRow{Type: RowSeparator},
			{
				Type:        RowSubtitle,
				CustomText:  "How: Enter your 18-digit Discord User ID.",
				CustomColor: Cyan,
			},
			{
				Type:        RowSubtitle,
				CustomText:  "Tip: Press [ENTER] to skip (no pings needed).",
				CustomColor: Dim,
			},
		})
		fmt.Printf("%s› Discord User ID (or [ENTER] for none): %s", pad+White, NC)
		mInput := strings.TrimSpace(readLine())
		if mInput != "" {
			if !strings.HasPrefix(mInput, "<@") {
				discordMention = fmt.Sprintf("<@%s>", mInput)
			} else {
				discordMention = mInput
			}
			saveDiscordMention(discordMention)
		}
	}
}

func configureSystemOptimizer() {
	drainInput()
	pad := getMenuLeftPad()
	res := getSystemResources()

	rows := []BoxRow{
		{
			Type:        RowSubtitle,
			CustomText:  "Reclaim RAM & CPU by closing unnecessary background apps.",
			CustomColor: White,
		},
		{
			Type:        RowSubtitle,
			CustomText:  fmt.Sprintf("Current Available RAM: %.1f GB / %.1f GB Total", res.AvailableRAMGB, res.TotalRAMGB),
			CustomColor: Cyan,
		},
		BoxRow{Type: RowSeparator},
		{
			Type:       RowKeyValue,
			Label:      "[1] Deep Clean  ",
			LabelColor: Green,
			Value:      "Close Background Apps + Flush Cache & Defrag RAM",
			ValueColor: Green,
		},
		{
			Type:       RowKeyValue,
			Label:      "[2] Light Clean ",
			LabelColor: White,
			Value:      "Purge Stale Clones + Flush Kernel Caches Only",
			ValueColor: Dim,
		},
		{
			Type:       RowKeyValue,
			Label:      "[3] Skip        ",
			LabelColor: White,
			Value:      "Keep all background apps running as-is",
			ValueColor: Dim,
		},
		BoxRow{Type: RowSeparator},
		{
			Type:        RowSubtitle,
			CustomText:  "Protected: Termux, Magisk/KernelSU, System UI & Keyboards",
			CustomColor: Dim,
		},
		{
			Type:        RowSubtitle,
			CustomText:  "Tip: Press [ENTER] for Deep Clean (Recommended)",
			CustomColor: Green,
		},
	}

	drawStepCard("5. SYSTEM OPTIMIZER & CLEANUP", "Reclaim RAM & CPU for Roblox Clones", rows)
	fmt.Printf("%s› Selection [1-3] (default: 1): %s", pad+White, NC)

	for {
		choice := strings.TrimSpace(readLine())
		if choice == "" || choice == "1" {
			cleanMode = CleanModeDeep
			cleanedModeDesc = "Deep Clean"
			break
		} else if choice == "2" {
			cleanMode = CleanModeLight
			cleanedModeDesc = "Light Clean"
			break
		} else if choice == "3" {
			cleanMode = CleanModeNone
			cleanedModeDesc = "Disabled"
			break
		}
		fmt.Printf("%s%sPlease enter 1, 2, or 3: %s", pad, Red, NC)
	}
}

func optimizeSystemAndCleanApps(mode CleanMode) (freedMB int, appsClosed int) {
	if mode == CleanModeNone {
		return 0, 0
	}

	resPre := getSystemResources()
	preAvailMB := resPre.AvailableRAMMB

	// Stage 1: Purge stale or lingering Roblox clones & temporary signal files
	for _, pkg := range allPackages {
		_ = exec.Command("am", "force-stop", pkg).Run()
		if checkRoot() {
			_ = exec.Command("su", "-c", "am force-stop "+pkg).Run()
		}
	}
	_ = os.Remove("/sdcard/nefarious_active_clone.txt")
	_ = os.Remove("/sdcard/nefarious_kick_signal.txt")
	_ = os.Remove("/sdcard/nefarious_events.log")

	// Stage 2: Deep background app termination
	if mode == CleanModeDeep {
		// Run Android native am kill-all (kills all safe background processes)
		if checkRoot() {
			_ = exec.Command("su", "-c", "am kill-all").Run()
		} else {
			_ = exec.Command("am", "kill-all").Run()
		}
		appsClosed++

		// Explicitly terminate common heavy resource-hogging background apps
		for _, pkg := range commonHeavyPackages {
			if isProtectedPackage(pkg) {
				continue
			}
			var err error
			if checkRoot() {
				err = exec.Command("su", "-c", "am force-stop "+pkg).Run()
			} else {
				err = exec.Command("am", "force-stop", pkg).Run()
			}
			if err == nil {
				appsClosed++
			}
		}
	}

	// Stage 3: Flush kernel page caches & compact memory fragmentation
	if checkRoot() {
		_ = exec.Command("su", "-c", "echo 3 > /proc/sys/vm/drop_caches").Run()
		_ = exec.Command("su", "-c", "echo 1 > /proc/sys/vm/compact_memory").Run()
		_ = exec.Command("su", "-c", "pm trim-caches 999999999").Run()
	} else {
		_ = exec.Command("pm", "trim-caches", "999999999").Run()
	}

	// Brief pause for kernel /proc/meminfo to refresh
	time.Sleep(500 * time.Millisecond)

	resPost := getSystemResources()
	postAvailMB := resPost.AvailableRAMMB
	freedMB = postAvailMB - preAvailMB
	if freedMB < 0 {
		freedMB = 0
	}

	cleanedRAMFreedMB = freedMB
	cleanedAppsCount = appsClosed

	currTime := time.Now().Format("15:04:05")
	safeLog("[%s] %s[OPTIMIZER]%s System cleanup complete. %d background targets processed | +%d MB RAM freed (Avail: %d MB)",
		currTime, Green, NC, appsClosed, freedMB, postAvailMB)
	writeLog("OPTIMIZER", fmt.Sprintf("Clean complete (%s). Targets: %d, Freed: +%d MB, Avail: %d MB",
		cleanedModeDesc, appsClosed, freedMB, postAvailMB))

	return freedMB, appsClosed
}

// ============================================================================
// INSTANCE LAUNCH & ORCHESTRATION
// ============================================================================

func launchInitialInstances() bool {
	// Pre-launch check: abort immediately if Delta upgrade is required
	if isDeltaUpdateAvailable() {
		handleDeltaUpgradeAbort("Pre-Launch Delta Check", nil)
		return false
	}

	// Pre-Launch System Optimization & Background App Purge
	if cleanMode != CleanModeNone {
		drawLaunchStatusCard(0, cloneCount, "System Optimization", "Purging background apps & defragmenting RAM...")
		freed, apps := optimizeSystemAndCleanApps(cleanMode)
		if freed > 0 {
			runAnimatedCountdown(fmt.Sprintf("System optimized (+%d MB freed, %d targets)...", freed, apps), 2, "CLEAN", fmt.Sprintf("Memory boosted (+%d MB freed)", freed))
		} else {
			runAnimatedCountdown("System optimized (Memory defragmented)...", 2, "CLEAN", "System clean & ready")
		}
	}

	for i := 0; i < cloneCount; i++ {
		// Check before launching each clone
		if isDeltaUpdateAvailable() {
			handleDeltaUpgradeAbort("Pre-Launch Delta Check", activePackages[:i])
			return false
		}
		if checkForUpgradeDialog() {
			handleDeltaUpgradeAbort("Roblox Upgrade Dialog Detected", activePackages[:i])
			return false
		}

		pkg := activePackages[i]
		displayName := fmt.Sprintf("Clone %d", i+1)

		recentlyLaunchedMu.Lock()
		recentlyLaunchedPkg = pkg
		recentlyLaunchedMu.Unlock()
		_ = os.WriteFile("/sdcard/nefarious_active_clone.txt", []byte(fmt.Sprintf("%s|%s", displayName, pkg)), 0644)

		markCloneLaunched(pkg)

		drawLaunchStatusCard(i+1, cloneCount, "Starting Client Engine", "Initializing APK engine...")
		var outLaunch []byte
		var errLaunch error
		outLaunch, errLaunch = exec.Command("am", "start", "-a", "android.intent.action.MAIN", "-c", "android.intent.category.LAUNCHER", "-p", pkg).CombinedOutput()
		if errLaunch != nil || strings.Contains(string(outLaunch), "Error") {
			safeLog("  %s[LAUNCH LOG]%s %s: %s", Amber, NC, displayName, strings.TrimSpace(string(outLaunch)))
		}
		time.Sleep(600 * time.Millisecond)
		hideSoftKeyboard()

		// Check if launching triggered the upgrade dialog
		if checkForUpgradeDialog() {
			handleDeltaUpgradeAbort("Roblox Upgrade Dialog Detected", activePackages[:i+1])
			return false
		}

		runAnimatedCountdown(fmt.Sprintf("Warming engine (%s)...", displayName), 8, "READY", fmt.Sprintf("Client engine ready (%s)", displayName))

		// Check again after warming engine before connecting to game
		if isDeltaUpdateAvailable() || checkForUpgradeDialog() {
			handleDeltaUpgradeAbort("Roblox Upgrade Detected During Warmup", activePackages[:i+1])
			return false
		}

		cloneGame := getCloneGameConfig(pkg)
		drawLaunchStatusCard(i+1, cloneCount, "Connecting to Game", fmt.Sprintf("Connecting to %s...", cloneGame.Name))
		var outJoin []byte
		var errJoin error
		if checkRoot() {
			cmdStr := fmt.Sprintf("am start -a android.intent.action.VIEW -d '%s' -p %s", cloneGame.URL, pkg)
			outJoin, errJoin = exec.Command("su", "-c", cmdStr).CombinedOutput()
		} else {
			outJoin, errJoin = exec.Command("am", "start", "-a", "android.intent.action.VIEW", "-d", cloneGame.URL, "-p", pkg).CombinedOutput()
		}
		if errJoin != nil || strings.Contains(string(outJoin), "Error") {
			safeLog("  %s[JOIN LOG]%s %s: %s", Amber, NC, displayName, strings.TrimSpace(string(outJoin)))
		}
		time.Sleep(600 * time.Millisecond)
		hideSoftKeyboard()

		// Check if connecting to game triggered upgrade dialog
		if checkForUpgradeDialog() {
			handleDeltaUpgradeAbort("Roblox Upgrade Dialog Detected", activePackages[:i+1])
			return false
		}

		if i < cloneCount-1 {
			drawLaunchStatusCard(i+1, cloneCount, "Stabilizing Memory", "Cooling down before launching next clone...")
			runAnimatedCountdown(fmt.Sprintf("Stabilizing memory (%s)...", displayName), 15, "STABLE", fmt.Sprintf("%s stabilized", displayName))
			if checkForUpgradeDialog() {
				handleDeltaUpgradeAbort("Roblox Upgrade Dialog Detected", activePackages[:i+1])
				return false
			}
		}
	}

	if enableRejoin {
		drawSentinelActiveCard()
	}
	return true
}

// ============================================================================
// SENTINEL ENGINE (CRASH / FREEZE / RECOVERY)
// ============================================================================

type RecoveryRequest struct {
	Pkg         string
	DisplayName string
	IsANR       bool
	Timestamp   string
}

var (
	recoveryQueueMu        sync.Mutex
	recoveryQueue          []RecoveryRequest
	currentlyRecoveringPkg string
	recoveryWorkerRunning  bool
)

func enqueueRecovery(pkg, displayName string, isANR bool) {
	networkMu.RLock()
	netUp := networkOnline
	networkMu.RUnlock()
	if !netUp {
		return
	}

	if isCloneRecoveringOrCooldown(pkg) {
		return
	}

	recoveringMu.Lock()
	if recoveringClones[pkg] {
		recoveringMu.Unlock()
		return
	}
	recoveringClones[pkg] = true
	recoveringMu.Unlock()

	recoveryQueueMu.Lock()
	alreadyQueued := false
	for _, req := range recoveryQueue {
		if req.Pkg == pkg {
			alreadyQueued = true
			break
		}
	}
	if !alreadyQueued && currentlyRecoveringPkg != pkg {
		recoveryQueue = append(recoveryQueue, RecoveryRequest{
			Pkg:         pkg,
			DisplayName: displayName,
			IsANR:       isANR,
			Timestamp:   time.Now().Format("15:04:05"),
		})
		safeLog("[%s] %s[QUEUE]%s    %s added to recovery queue (%d pending in queue)...",
			time.Now().Format("15:04:05"), Amber, NC, displayName, len(recoveryQueue))
	}
	syncDashboardQueueState()

	startWorker := false
	if !recoveryWorkerRunning {
		recoveryWorkerRunning = true
		startWorker = true
	}
	recoveryQueueMu.Unlock()

	if startWorker {
		go recoveryWorkerLoop()
	}

	dashboardMu.Lock()
	active := isMonitoringActive
	hasCountdown := currentDashboard.ActionStep != ""
	dashboardMu.Unlock()
	if active && !hasCountdown {
		drawSummaryCard()
	}
}

func syncDashboardQueueState() {
	var queuedNames []string
	for _, req := range recoveryQueue {
		queuedNames = append(queuedNames, req.DisplayName)
	}

	dashboardMu.Lock()
	if len(queuedNames) > 0 {
		currentDashboard.QueueInfo = fmt.Sprintf("%d Pending (%s)", len(queuedNames), strings.Join(queuedNames, ", "))
		if currentlyRecoveringPkg != "" {
			activeName := getCloneDisplayName(currentlyRecoveringPkg)
			currentDashboard.Status = fmt.Sprintf("Recovering: %s (%d Queued)", activeName, len(queuedNames))
			currentDashboard.StatusColor = Amber
		} else {
			currentDashboard.Status = fmt.Sprintf("Crash Detected (%d Queued)", len(queuedNames))
			currentDashboard.StatusColor = Red
		}
	} else {
		currentDashboard.QueueInfo = ""
		if currentlyRecoveringPkg != "" {
			activeName := getCloneDisplayName(currentlyRecoveringPkg)
			currentDashboard.Status = "Recovering: " + activeName
			currentDashboard.StatusColor = Cyan
		}
	}
	dashboardMu.Unlock()
}

func recoveryWorkerLoop() {
	for {
		recoveryQueueMu.Lock()
		if len(recoveryQueue) == 0 {
			currentlyRecoveringPkg = ""
			recoveryWorkerRunning = false
			syncDashboardQueueState()
			recoveryQueueMu.Unlock()

			dashboardMu.Lock()
			active := isMonitoringActive
			hasCountdown := currentDashboard.ActionStep != ""
			dashboardMu.Unlock()
			if active && !hasCountdown {
				drawSummaryCard()
			}
			return
		}

		req := recoveryQueue[0]
		recoveryQueue = recoveryQueue[1:]
		currentlyRecoveringPkg = req.Pkg
		syncDashboardQueueState()
		recoveryQueueMu.Unlock()

		dashboardMu.Lock()
		active := isMonitoringActive
		hasCountdown := currentDashboard.ActionStep != ""
		dashboardMu.Unlock()
		if active && !hasCountdown {
			drawSummaryCard()
		}

		executeCloneRecovery(req.Pkg, req.DisplayName, req.IsANR)

		recoveringMu.Lock()
		delete(recoveringClones, req.Pkg)
		recoveringMu.Unlock()

		// Apply 30s post-recovery cooldown to eliminate residual/trailing logcat re-triggers
		setCloneRecoveryCooldown(req.Pkg, 30*time.Second)
	}
}

func recoverClone(pkg, displayName string, isANR bool) {
	enqueueRecovery(pkg, displayName, isANR)
}

func executeCloneRecovery(pkg, displayName string, isANR bool) {
	networkMu.RLock()
	netUp := networkOnline
	networkMu.RUnlock()
	if !netUp {
		return
	}

	if isDeltaUpdateAvailable() || checkForUpgradeDialog() {
		handleDeltaUpgradeAbort("Sentinel Watchdog Recovery", []string{pkg})
		return
	}

	eventTime := time.Now().Format("15:04:05")
	logTimestamp := time.Now().Format("2006-01-02 15:04:05")

	// Refresh live system resources
	res := getSystemResources()
	cloneGame := getCloneGameConfig(pkg)
	cloneMem := getCloneMemoryUsage(pkg, cloneGame.Name)

	ramDesc := fmt.Sprintf("~%d MB (%s)", cloneMem.RAMMB, cloneMem.GameProfile)
	if !cloneMem.IsEstimated && cloneMem.PID > 0 {
		ramDesc = fmt.Sprintf("%d MB RSS (PID %d)", cloneMem.RAMMB, cloneMem.PID)
	}

	if isANR {
		setDashboardEvent("Recovering: "+displayName, Amber, "ANR", displayName+" Unresponsive", ramDesc, eventTime)
		safeLog("[%s] %s[ANR]%s      %s%s%s unresponsive (freeze). Rebooting...", eventTime, Amber, NC, White, displayName, NC)
		writeLog("ANR", fmt.Sprintf("%s unresponsive", displayName))
		sendFreezeWebhook(displayName, pkg, cloneGame.Name, res, cloneMem, logTimestamp)
	} else {
		setDashboardEvent("Recovering: "+displayName, Red, "CRASH", displayName+" Terminated", ramDesc, eventTime)
		if !cloneMem.IsEstimated && cloneMem.PID > 0 {
			safeLog("[%s] %s[CRASH]%s    %s%s%s process terminated (Last RAM: %d MB, PID: %d). Recovering...", eventTime, Red, NC, White, displayName, NC, cloneMem.RAMMB, cloneMem.PID)
		} else {
			safeLog("[%s] %s[CRASH]%s    %s%s%s process terminated. Recovering...", eventTime, Red, NC, White, displayName, NC)
		}
		writeLog("CRASH", fmt.Sprintf("%s terminated", displayName))
		sendCrashWebhook(displayName, pkg, cloneGame.Name, res, cloneMem, logTimestamp)
	}

	// Live Resource display on console
	safeLog("[%s] %s[RESOURCE]%s  RAM: %s%.1f/%.1f GB (%.0f%%)%s | CPU: %s%.1f%%%s",
		eventTime, Cyan, NC, White, res.UsedRAMGB, res.TotalRAMGB, res.RAMUsagePercent, NC, White, res.CPUUsagePercent, NC)

	// Queue recovery so multiple instances don't spike CPU/RAM simultaneously
	globalRecoveryLock.Lock()
	defer globalRecoveryLock.Unlock()

	networkMu.RLock()
	netUp = networkOnline
	networkMu.RUnlock()
	if !netUp {
		return
	}

	setDashboardEvent("Recovering: "+displayName, Cyan, "RECOVERING", displayName+" Restarting...", ramDesc, time.Now().Format("15:04:05"))

	// 1. Force-stop to clear stuck instance
	_ = exec.Command("am", "force-stop", pkg).Run()
	time.Sleep(1 * time.Second)

	recentlyLaunchedMu.Lock()
	recentlyLaunchedPkg = pkg
	recentlyLaunchedMu.Unlock()
	_ = os.WriteFile("/sdcard/nefarious_active_clone.txt", []byte(fmt.Sprintf("%s|%s", displayName, pkg)), 0644)

	// 2. Launch client engine
	markCloneLaunched(pkg)
	_ = exec.Command("am", "start", "-a", "android.intent.action.MAIN", "-c", "android.intent.category.LAUNCHER", "-p", pkg).Run()
	time.Sleep(600 * time.Millisecond)
	hideSoftKeyboard()

	// 3. Full 10-second client engine initialization animated countdown
	runAnimatedCountdown(fmt.Sprintf("Initializing client engine (%s)...", displayName), 10, "READY", fmt.Sprintf("Client engine initialized (%s)", displayName))

	// 4. Game connection intent
	joinTime := time.Now().Format("15:04:05")
	safeLog("[%s] %s[JOIN]%s     Connecting %s%s%s to %s%s%s...", joinTime, Cyan, NC, White, displayName, NC, White, cloneGame.Name, NC)
	if checkRoot() {
		cmdStr := fmt.Sprintf("am start -a android.intent.action.VIEW -d '%s' -p %s", cloneGame.URL, pkg)
		_ = exec.Command("su", "-c", cmdStr).Run()
	} else {
		_ = exec.Command("am", "start", "-a", "android.intent.action.VIEW", "-d", cloneGame.URL, "-p", pkg).Run()
	}
	time.Sleep(600 * time.Millisecond)
	hideSoftKeyboard()

	reopenTime := time.Now().Format("15:04:05")
	safeLog("[%s] %s[OK]%s       %s%s%s synchronized with %s", reopenTime, Green, NC, White, displayName, NC, cloneGame.Name)
	writeLog("RESTORE", fmt.Sprintf("%s recovered", displayName))

	// 5. Staggered stabilization countdown
	runAnimatedCountdown(fmt.Sprintf("Cooling down (%s)...", displayName), 20, "READY", fmt.Sprintf("Cooldown complete (%s)", displayName))

	stableTime := time.Now().Format("15:04:05")
	writeLog("STABLE", fmt.Sprintf("%s verified online", displayName))

	res2 := getSystemResources()
	var cloneMem2 CloneResourceReport
	for attempt := 0; attempt < 4; attempt++ {
		cloneMem2 = getCloneMemoryUsage(pkg, cloneGame.Name)
		if !cloneMem2.IsEstimated && cloneMem2.PID > 0 {
			break
		}
		time.Sleep(1 * time.Second)
	}

	restoredRAMDesc := fmt.Sprintf("~%d MB (%s)", cloneMem2.RAMMB, cloneMem2.GameProfile)
	if !cloneMem2.IsEstimated && cloneMem2.PID > 0 {
		restoredRAMDesc = fmt.Sprintf("%d MB RSS (PID %d)", cloneMem2.RAMMB, cloneMem2.PID)
	}

	setDashboardEvent("Active - "+displayName+" Restored", Green, "RESTORED", displayName+" Resynchronized", restoredRAMDesc, stableTime)

	if !cloneMem2.IsEstimated && cloneMem2.PID > 0 {
		safeLog("[%s] %s[STABLE]%s   %s%s%s online (RAM: %d MB, PID: %d). Monitoring resumed.", stableTime, Green, NC, White, displayName, NC, cloneMem2.RAMMB, cloneMem2.PID)
	} else {
		safeLog("[%s] %s[STABLE]%s   %s%s%s online. Monitoring resumed.", stableTime, Green, NC, White, displayName, NC)
	}

	sendRecoveryWebhook(displayName, pkg, cloneGame.Name, res2, cloneMem2)

	// Post-recovery stabilization: do not touch or re-tile other running clones to prevent ping-pong reopen loops

	// Check if more clones are waiting in queue
	recoveryQueueMu.Lock()
	hasMore := len(recoveryQueue) > 0
	recoveryQueueMu.Unlock()

	if hasMore {
		// Immediately proceed to next queued clone
		time.Sleep(1 * time.Second)
	} else {
		// Queue is empty: display restored status for 5 seconds, then return to normal monitoring
		time.Sleep(5 * time.Second)
		recoveryQueueMu.Lock()
		moreQueued := len(recoveryQueue) > 0
		recoveryQueueMu.Unlock()
		if !moreQueued {
			clearDashboardEvent()
			setDashboardStatus("Monitoring 24/7 (Auto-Rejoin)", Green)
		}
	}
}

func startSentinelMonitor() {
	time.Sleep(5 * time.Second)
	_ = exec.Command("logcat", "-c").Run()
	time.Sleep(1 * time.Second)

	filterRegex := regexp.MustCompile(`WIN DEATH|has died|am_crash|ANR in|am_anr|Error Code: 273|Error Code: 277|Same account launched|Disconnected from`)
	anrRegex := regexp.MustCompile(`ANR in|am_anr`)
	disconnectRegex := regexp.MustCompile(`Error Code: 273|Error Code: 277|Same account launched|Disconnected from`)

	for {
		cmd := exec.Command("logcat")
		stdout, err := cmd.StdoutPipe()
		if err != nil {
			time.Sleep(2 * time.Second)
			continue
		}
		if err := cmd.Start(); err != nil {
			time.Sleep(2 * time.Second)
			continue
		}

		scanner := bufio.NewScanner(stdout)
		for scanner.Scan() {
			line := scanner.Text()
			if !filterRegex.MatchString(line) {
				continue
			}

			// Ignore individual crash events if network is offline
			networkMu.RLock()
			netUp := networkOnline
			networkMu.RUnlock()
			if !netUp {
				continue
			}

			for i, pkg := range activePackages {
				matchesPkg := strings.Contains(line, pkg)
				if !matchesPkg && disconnectRegex.MatchString(line) {
					if cached, ok := telemetryStore.Get(pkg); ok && cached.PID > 0 {
						if strings.Contains(line, strconv.Itoa(cached.PID)) {
							matchesPkg = true
						}
					}
					if !matchesPkg {
						out, err := exec.Command("pidof", pkg).Output()
						if err == nil {
							pids := strings.Fields(string(out))
							for _, pid := range pids {
								if pid != "" && strings.Contains(line, pid) {
									matchesPkg = true
									break
								}
							}
						}
					}
				}

				if matchesPkg {
					if isCloneRecoveringOrCooldown(pkg) {
						continue
					}
					cloneNum := i + 1
					displayName := fmt.Sprintf("Clone %d", cloneNum)
					isANR := anrRegex.MatchString(line)
					enqueueRecovery(pkg, displayName, isANR)
				}
			}
		}
		_ = cmd.Wait()
		time.Sleep(2 * time.Second)
	}
}

// ============================================================================
// NETWORK INTEGRITY & CONNECTION MONITOR
// ============================================================================

func isInternetConnected() bool {
	conn, err := net.DialTimeout("tcp", "1.1.1.1:443", 2*time.Second)
	if err == nil {
		_ = conn.Close()
		return true
	}
	conn2, err2 := net.DialTimeout("tcp", "8.8.8.8:53", 2*time.Second)
	if err2 == nil {
		_ = conn2.Close()
		return true
	}
	return false
}

func waitForInternetAtStartup() {
	if isInternetConnected() {
		return
	}

	safeLog("%s[OFFLINE]%s No internet connection detected.", Red, NC)

	s := &spinnerState{
		label:     "Waiting for network connection...",
		remaining: -1,
	}

	consoleMu.Lock()
	activeSpinner = s
	s.renderUnsafe()
	consoleMu.Unlock()

	ticker := time.NewTicker(80 * time.Millisecond)
	defer ticker.Stop()

	for {
		select {
		case <-ticker.C:
			consoleMu.Lock()
			if activeSpinner == s && !s.done {
				s.frameIdx++
				s.renderUnsafe()
			}
			consoleMu.Unlock()
		default:
			if isInternetConnected() {
				consoleMu.Lock()
				s.done = true
				if activeSpinner == s {
					activeSpinner = nil
				}
				fmt.Print("\r\033[K")
				fmt.Printf("  %s[CONNECTED]%s Internet connection established.\n\n", Green, NC)
				consoleMu.Unlock()
				time.Sleep(1 * time.Second)
				return
			}
			time.Sleep(500 * time.Millisecond)
		}
	}
}

func getPublicIP() (string, error) {
	client := &http.Client{Timeout: 4 * time.Second}
	resp, err := client.Get("https://1.1.1.1/cdn-cgi/trace")
	if err == nil {
		defer resp.Body.Close()
		body, _ := io.ReadAll(resp.Body)
		lines := strings.Split(string(body), "\n")
		for _, l := range lines {
			if strings.HasPrefix(l, "ip=") {
				ip := strings.TrimSpace(strings.TrimPrefix(l, "ip="))
				if ip != "" {
					return ip, nil
				}
			}
		}
	}

	resp2, err2 := client.Get("https://api.ipify.org")
	if err2 == nil {
		defer resp2.Body.Close()
		body, _ := io.ReadAll(resp2.Body)
		ip := strings.TrimSpace(string(body))
		if ip != "" {
			return ip, nil
		}
	}

	return "", fmt.Errorf("network unreachable")
}

func relaunchAllClones(reason string) {
	globalRecoveryLock.Lock()
	defer globalRecoveryLock.Unlock()

	recoveryQueueMu.Lock()
	recoveryQueue = nil
	currentlyRecoveringPkg = ""
	recoveryQueueMu.Unlock()

	setDashboardStatus("Relaunching Clones ("+reason+")", Amber)

	recoveringMu.Lock()
	recoveringClones = make(map[string]bool)
	for _, pkg := range activePackages {
		recoveringClones[pkg] = true
	}
	recoveringMu.Unlock()

	for _, pkg := range activePackages {
		_ = exec.Command("am", "force-stop", pkg).Run()
	}
	time.Sleep(2 * time.Second)

	for i, pkg := range activePackages {
		displayName := fmt.Sprintf("Clone %d", i+1)
		nowTime := time.Now().Format("15:04:05")
		safeLog("[%s] %s[RELOAD]%s    Relaunching %s%s%s after %s...", nowTime, Cyan, NC, White, displayName, NC, reason)

		recentlyLaunchedMu.Lock()
		recentlyLaunchedPkg = pkg
		recentlyLaunchedMu.Unlock()
		_ = os.WriteFile("/sdcard/nefarious_active_clone.txt", []byte(fmt.Sprintf("%s|%s", displayName, pkg)), 0644)

		markCloneLaunched(pkg)
		_ = exec.Command("am", "start", "-a", "android.intent.action.MAIN", "-c", "android.intent.category.LAUNCHER", "-p", pkg).Run()
		runAnimatedCountdown(fmt.Sprintf("Warming client engine (%s)...", displayName), 8, "READY", fmt.Sprintf("Client engine ready (%s)", displayName))

		_ = exec.Command("am", "start", "-a", "android.intent.action.VIEW", "-d", gameURL, "-p", pkg).Run()

		if i < cloneCount-1 {
			runAnimatedCountdown(fmt.Sprintf("Stabilizing memory (%s)...", displayName), 15, "STABLE", fmt.Sprintf("%s stabilized", displayName))
		}
	}

	recoveringMu.Lock()
	recoveringClones = make(map[string]bool)
	recoveringMu.Unlock()

	for _, pkg := range activePackages {
		setCloneRecoveryCooldown(pkg, 30*time.Second)
	}


	safeLog("\n%s[ALL RESTORED] All %d Roblox clones successfully recovered after %s.%s\n", Green, cloneCount, reason, NC)
	writeLog("ALL_RESTORED", fmt.Sprintf("All %d clones recovered after %s.", cloneCount, reason))
	sendWebhook("All Clones Restored", fmt.Sprintf("All %d Roblox clones successfully recovered after %s.", cloneCount, reason), 3066993)
	setDashboardStatus(fmt.Sprintf("Restored: All %d Clones Online", cloneCount), Green)
}

func startNetworkMonitor() {
	var lastIP string
	wasOnline := isInternetConnected()

	if wasOnline {
		if ip, err := getPublicIP(); err == nil {
			lastIP = ip
		}
	}

	ticker := time.NewTicker(4 * time.Second)
	defer ticker.Stop()

	offlineTick := 0

	for range ticker.C {
		connected := isInternetConnected()
		var currentIP string
		if connected {
			if ip, err := getPublicIP(); err == nil {
				currentIP = ip
			} else {
				currentIP = lastIP
			}
		}

		isOnline := (connected && currentIP != "")

		// Case 1: Internet connection lost
		if wasOnline && !isOnline {
			wasOnline = false
			networkMu.Lock()
			networkOnline = false
			networkMu.Unlock()
			setDashboardStatus("Offline: Connection Lost", Red)

			nowTime := time.Now().Format("15:04:05")
			safeLog("\n[%s] %s[LOST CONNECTION]%s Internet connection lost! Force-stopping all clones...", nowTime, Red, NC)
			writeLog("NET_DISCONNECT", "Internet connection lost. Force-stopping all clones.")
			sendRichWebhook(EventNetwork, "Lost Connection", "Internet connection lost. Force-stopping all Roblox clones to prevent freeze.", 15158332, nil)

			globalRecoveryLock.Lock()
			for _, pkg := range activePackages {
				_ = exec.Command("am", "force-stop", pkg).Run()
			}
			globalRecoveryLock.Unlock()
			offlineTick = 0
			continue
		}

		// Periodic status while offline
		if !isOnline {
			offlineTick++
			if offlineTick%6 == 0 {
				currTime := time.Now().Format("15:04:05")
				safeLog("[%s] %s[LOST CONNECTION]%s Waiting for network connection to restore...", currTime, Gray, NC)
			}
			continue
		}

		// Case 2: Internet reconnected after outage
		if !wasOnline && isOnline {
			wasOnline = true
			networkMu.Lock()
			networkOnline = true
			networkMu.Unlock()
			setDashboardStatus("Online: Connection Restored", Green)

			nowTime := time.Now().Format("15:04:05")
			safeLog("\n[%s] %s[CONNECTION RESTORED]%s Internet reconnected. Relaunching all clones...", nowTime, Green, NC)
			writeLog("NET_RECONNECT", "Internet connection restored. Relaunching all clones.")
			sendRichWebhook(EventNetwork, "Connection Restored", "Internet connection restored. Relaunching and resynchronizing all clones.", 3066993, nil)

			lastIP = currentIP
			relaunchAllClones("Connection Restored")
			continue
		}

		// Case 3: Public IP changed while online
		if isOnline && lastIP != "" && currentIP != lastIP {
			nowTime := time.Now().Format("15:04:05")
			safeLog("\n[%s] %s[IP CHANGED]%s IP switch detected. Force-stopping and relaunching clones...", nowTime, Amber, NC)
			writeLog("IP_CHANGE", fmt.Sprintf("IP changed from %s to %s. Relaunching all clones.", lastIP, currentIP))
			sendWebhook("IP Change Detected", "Device IP network route changed. Force-stopping and relaunching all clones...", 15105570)

			lastIP = currentIP
			relaunchAllClones("Network IP Route Changed")
			continue
		}

		if isOnline && lastIP == "" {
			lastIP = currentIP
		}
	}
}

// ============================================================================
// LOCAL BRIDGE HTTP SERVER & SIGNAL SUBSYSTEMS
// ============================================================================

func startLocalBridgeServer() {
	mux := http.NewServeMux()

	// 1. Handshake endpoint
	mux.HandleFunc("/handshake", func(w http.ResponseWriter, r *http.Request) {
		player := strings.TrimSpace(r.URL.Query().Get("player"))

		recentlyLaunchedMu.Lock()
		assignedPkg := recentlyLaunchedPkg
		recentlyLaunchedMu.Unlock()

		if assignedPkg == "" && len(activePackages) > 0 {
			assignedPkg = activePackages[0]
		}

		cloneIdx := 1
		for i, p := range activePackages {
			if p == assignedPkg {
				cloneIdx = i + 1
				break
			}
		}

		if player != "" {
			playerPkgMu.Lock()
			playerPkgMap[player] = assignedPkg
			playerPkgMu.Unlock()
		}

		currTime := time.Now().Format("15:04:05")
		safeLog("[%s] %s[CONNECT]%s   Clone %d bound to player: %s%s%s",
			currTime, Green, NC, cloneIdx, White, player, NC)

		w.Header().Set("Content-Type", "application/json")
		_ = json.NewEncoder(w).Encode(map[string]interface{}{
			"status": "ok",
			"pkg":    assignedPkg,
			"clone":  cloneIdx,
		})
	})

	// Legacy /register fallback
	mux.HandleFunc("/register", func(w http.ResponseWriter, r *http.Request) {
		player := strings.TrimSpace(r.URL.Query().Get("player"))
		if player != "" {
			recentlyLaunchedMu.Lock()
			assignedPkg := recentlyLaunchedPkg
			recentlyLaunchedMu.Unlock()

			if assignedPkg == "" && len(activePackages) > 0 {
				assignedPkg = activePackages[0]
			}

			playerPkgMu.Lock()
			playerPkgMap[player] = assignedPkg
			playerPkgMu.Unlock()
		}
		w.WriteHeader(http.StatusOK)
		_, _ = w.Write([]byte("OK"))
	})

	// 2. Heartbeat endpoint
	mux.HandleFunc("/heartbeat", func(w http.ResponseWriter, r *http.Request) {
		w.WriteHeader(http.StatusOK)
		_, _ = w.Write([]byte("PONG"))
	})

	// 3. Report endpoint
	mux.HandleFunc("/report", func(w http.ResponseWriter, r *http.Request) {
		pkgParam := strings.TrimSpace(r.URL.Query().Get("pkg"))
		player := strings.TrimSpace(r.URL.Query().Get("player"))
		reason := strings.TrimSpace(r.URL.Query().Get("reason"))
		detail := strings.TrimSpace(r.URL.Query().Get("detail"))

		w.WriteHeader(http.StatusOK)
		_, _ = w.Write([]byte("RECEIVED"))

		if reason == "" {
			return
		}

		targetPkg := pkgParam
		if targetPkg == "" && player != "" {
			playerPkgMu.RLock()
			targetPkg = playerPkgMap[player]
			playerPkgMu.RUnlock()
		}
		if targetPkg == "" {
			recentlyLaunchedMu.Lock()
			targetPkg = recentlyLaunchedPkg
			recentlyLaunchedMu.Unlock()
		}
		if targetPkg == "" && len(activePackages) > 0 {
			targetPkg = activePackages[0]
		}

		displayName := getCloneDisplayName(targetPkg)

		if isCloneRecoveringOrCooldown(targetPkg) {
			return
		}

		currTime := time.Now().Format("15:04:05")
		safeLog("\n[%s] %s[ALERT]%s     %s%s%s reported: %s%s%s (%s)",
			currTime, Red, NC, White, displayName, NC, Amber, reason, NC, detail)
		writeLog("ERROR", fmt.Sprintf("%s: %s - %s", displayName, reason, detail))

		sendWebhook("In-Game Kick / Disconnect",
			fmt.Sprintf("**%s**\n**Player:** `%s`\n**Status:** `%s`\n**Detail:** ```%s```\nForce-stopping and relaunching...",
				displayName, player, reason, truncate(detail, 500)),
			15158332)

		enqueueRecovery(targetPkg, displayName, false)
	})

	// 4. Log endpoint
	mux.HandleFunc("/log", func(w http.ResponseWriter, r *http.Request) {
		player := strings.TrimSpace(r.URL.Query().Get("player"))
		tag := strings.TrimSpace(r.URL.Query().Get("tag"))
		msg := strings.TrimSpace(r.URL.Query().Get("msg"))
		pkgParam := strings.TrimSpace(r.URL.Query().Get("pkg"))
		cloneParam := strings.TrimSpace(r.URL.Query().Get("clone"))

		w.WriteHeader(http.StatusOK)
		_, _ = w.Write([]byte("OK"))

		if msg == "" {
			return
		}

		targetPkg := pkgParam
		if targetPkg == "" && player != "" {
			playerPkgMu.RLock()
			targetPkg = playerPkgMap[player]
			playerPkgMu.RUnlock()
		}
		if targetPkg == "" {
			recentlyLaunchedMu.Lock()
			targetPkg = recentlyLaunchedPkg
			recentlyLaunchedMu.Unlock()
		}
		if targetPkg == "" && len(activePackages) > 0 {
			targetPkg = activePackages[0]
		}

		displayName := getCloneDisplayName(targetPkg)
		if cloneParam != "" {
			displayName = fmt.Sprintf("Clone %s", cloneParam)
		}

		currTime := time.Now().Format("15:04:05")
		tagColor := Cyan
		if strings.Contains(tag, "RECONNECT") {
			tagColor = Amber
		} else if strings.Contains(tag, "KICK") || strings.Contains(tag, "ERROR") {
			tagColor = Red
		} else if strings.Contains(tag, "SUCCESS") || strings.Contains(tag, "OK") {
			tagColor = Green
		}

		if player != "" {
			safeLog("[%s] %s[%s]%s %s%s%s (%s): %s", currTime, tagColor, tag, NC, White, displayName, NC, player, msg)
		} else {
			safeLog("[%s] %s[%s]%s %s%s%s: %s", currTime, tagColor, tag, NC, White, displayName, NC, msg)
		}
		writeLog(tag, fmt.Sprintf("%s: %s", displayName, msg))
	})

	// 5. Ask AI endpoint
	mux.HandleFunc("/ask_ai", func(w http.ResponseWriter, r *http.Request) {
		player := strings.TrimSpace(r.URL.Query().Get("player"))
		cloneParam := strings.TrimSpace(r.URL.Query().Get("clone"))
		query := strings.TrimSpace(r.URL.Query().Get("query"))
		if query == "" {
			query = strings.TrimSpace(r.URL.Query().Get("q"))
		}

		w.WriteHeader(http.StatusOK)
		_, _ = w.Write([]byte("OK"))

		if query != "" {
			sendAskAIWebhook(player, cloneParam, query)
		}
	})

	server := &http.Server{
		Addr:    ":21420",
		Handler: mux,
	}

	_ = server.ListenAndServe()
}

func startCloudSignalPoller() {
	// Remote cloud signal polling disabled for open-source / local-only operation.
}

func startEventLogWatcher() {
	logPath := "/sdcard/nefarious_events.log"
	_ = os.Remove(logPath)

	var lastOffset int64 = 0
	for {
		time.Sleep(500 * time.Millisecond)
		fi, err := os.Stat(logPath)
		if err != nil || fi.Size() <= lastOffset {
			continue
		}

		f, err := os.Open(logPath)
		if err != nil {
			continue
		}
		_, _ = f.Seek(lastOffset, 0)
		scanner := bufio.NewScanner(f)
		for scanner.Scan() {
			line := strings.TrimSpace(scanner.Text())
			if line == "" {
				continue
			}

			currTime := time.Now().Format("15:04:05")
			tagColor := Cyan
			if strings.Contains(line, "RECONNECT") {
				tagColor = Amber
			} else if strings.Contains(line, "KICK") || strings.Contains(line, "ERROR") {
				tagColor = Red
			} else if strings.Contains(line, "SUCCESS") {
				tagColor = Green
			}

			safeLog("[%s] %s[SENTINEL]%s  %s", currTime, tagColor, NC, cleanSentinelLogLine(line))
			writeLog("SENTINEL_LOG", line)

			if strings.Contains(line, "KICK_DETECTED") || strings.Contains(line, "RECONNECT_FAILED") {
				for i, p := range activePackages {
					cloneTag := fmt.Sprintf("Clone %d", i+1)
					if strings.Contains(line, cloneTag) || strings.Contains(line, p) {
						if isCloneRecoveringOrCooldown(p) {
							continue
						}
						sendWebhook("In-Game Kick Signal",
							fmt.Sprintf("Sentinel detected kick signal for **%s** in **%s**. Initiating automated auto-rejoin...", cloneTag, gameName),
							15158332)
						enqueueRecovery(p, cloneTag, false)
					}
				}
			}
		}
		lastOffset, _ = f.Seek(0, io.SeekCurrent)
		_ = f.Close()
	}
}

func startKickSignalWatcher() {
	signalFile := "/sdcard/nefarious_kick_signal.txt"
	for {
		time.Sleep(500 * time.Millisecond)
		data, err := os.ReadFile(signalFile)
		if err != nil || len(data) == 0 {
			continue
		}
		_ = os.Remove(signalFile)

		raw := strings.TrimSpace(string(data))
		parts := strings.Split(raw, "|")
		targetPkg := parts[0]
		displayName := getCloneDisplayName(targetPkg)
		if len(parts) > 1 && strings.TrimSpace(parts[1]) != "" {
			candidate := strings.TrimSpace(parts[1])
			if strings.Contains(candidate, "Clone") {
				displayName = candidate
			}
		}
		if targetPkg == "" && len(activePackages) > 0 {
			targetPkg = activePackages[0]
			displayName = "Clone 1"
		}

		if isCloneRecoveringOrCooldown(targetPkg) {
			continue
		}

		currTime := time.Now().Format("15:04:05")
		safeLog("\n[%s] %s[AUTO-REJOIN]%s %s disconnected. Rejoining %s%s%s...",
			currTime, Amber, NC, displayName, White, gameName, NC)

		sendWebhook("In-Game Disconnect Detected",
			fmt.Sprintf("**%s** disconnected from **%s**. Initiating automated recovery sequence...", displayName, gameName),
			15158332)

		enqueueRecovery(targetPkg, displayName, false)
	}
}

// ============================================================================
// MAIN ENTRYPOINT
// ============================================================================

func main() {
	c := make(chan os.Signal, 1)
	signal.Notify(c, os.Interrupt, syscall.SIGTERM)
	go func() {
		<-c
		fmt.Println("\nSession terminated by user.")
		os.Exit(0)
	}()

	initResizeWatcher()
	initInputReader()

	myHWID = getDeviceHWID()

	drawBanner()
	waitForInternetAtStartup()
	checkUpdates()
	verifyLicense()

	drawBanner()
	configureConcurrency()
	configureTargetExperience()
	configureSentinel()
	configureWebhook()
	configureSystemOptimizer()

	drawBanner()
	drawSummaryCard()
	fmt.Println()

	hideSoftKeyboard()
	launched := launchInitialInstances()
	hideSoftKeyboard()

	if !launched {
		return
	}

	setDashboardStatus("Monitoring 24/7 (Auto-Rejoin)", Green)

	dashboardMu.Lock()
	isMonitoringActive = true
	dashboardMu.Unlock()

	drawSummaryCard()
	hideSoftKeyboard()

	sendSessionStartWebhook()

	if enableRejoin {
		go startLocalBridgeServer()
		go startCloudSignalPoller()
		go startEventLogWatcher()
		go startKickSignalWatcher()
		go startNetworkMonitor()
		go startResourceMonitor()
		go startTelemetrySampler()
		go startDeltaUpdatePoller()
		startSentinelMonitor()
	} else {
		select {}
	}
}

