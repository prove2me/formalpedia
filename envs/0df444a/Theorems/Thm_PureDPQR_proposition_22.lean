-- Prove2me | Theorems.Thm_PureDPQR_proposition_22
-- name    : PureDPQR.proposition_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T08:00:37.828793+00:00
-- url     : https://prove2.me/theorems/122ea2ae-aabd-477e-8162-09ad58ad149b
-- title:
--   Proposition 22, p.25 — Algorithm 2 and its internal transcript law $Q_h$ are pure $\varepsilon$-DP
-- statement:
--   **Proposition 22** (Privacy). Let $N\ge1$, $d\ge2$, $k\ge1$, $0<\varepsilon\le1$, $0<\beta<\frac12$ (the ranges of Theorem 2, assumed throughout §6), and let $Q=\{q_i\}_{i\in[k]}\subset[0,1]^d$. Then Algorithm 2 is pure $\varepsilon$-differentially private under record replacement: for all adjacent $h\sim h'$ in $H_{N,d}$ and every Borel set $F\subseteq\mathbb R^d$,
--
--   $$\Pr\{\hat p(h)\in F\}\le e^{\varepsilon}\Pr\{\hat p(h')\in F\}.$$
--
--   The same guarantee holds for its internal transcript law $Q_h=\mathbb E_Z[p_{h+Z}]$ on $[K]^T$: $Q_h(F)\le e^\varepsilon Q_{h'}(F)$ for every set of transcripts $F$.
--
--   This is the privacy half of Theorem 2.
--
--   **Formalization Note** The output law is `alg2Law`, the transcript law `transcriptLaw` (on a finite discrete space, so every set of transcripts is an event).
--
--   Differences from the source:
--   - encoding: adjacency h′ = h + e_a − e_b on ℕ^d → h′ + e_b = h + e_a; reason: no truncated subtraction; the same pairs
--   - encoding: Lap(κ) of rate κ → PrivLearn.Generic.laplace κ⁻¹ (scale parameter); reason: the published Laplace law is parametrized by its scale; same law
--   - encoding: measurable transcript events F ⊆ [K]^T → every set of transcripts, as a measurable set of the discrete σ-algebra on Fin T → Fin (2k); reason: the transcript space is finite; same events
--   - encoding: Algorithm 2, a randomized procedure → its laws: alg2Law = Σ_y Q_h(y) δ_{D(y)} and transcriptLaw = Σ_y Q_h(y) δ_y, with Q_h(y) the integral smoothed; reason: Z_j = B_j L_j has law (1−π)δ₀ + πLap(κ) and y given Z has law p_{h+Z}, so these are the laws of the procedure
--   - encoding: 1-based labels, coordinates and rounds → Fin (2k), Fin d, Fin T; reason: Lean convention
-- source:
--   Zou, Pure Differentially Private Query Release via Laplace Input Smoothing, arXiv:2611.04721 (held version, sha256 69b70d59…), Proposition 22, p.25 (PDF p.26); Algorithm 2, p.25; §6 preamble, p.25

import Mathlib
import Definitions.Def_PureDPQR_IsDP
import Definitions.Def_PureDPQR_alg2Law

namespace PureDPQR

/-- **Proposition 22** (Privacy), p.25 (PDF p.26).

Z. Zou, *Pure Differentially Private Query Release via Laplace Input Smoothing*, arXiv:2611.04721
(held version, sha256 69b70d59…).

"Algorithm 2 is pure ε-differentially private under record replacement. In particular, the same
privacy guarantee holds for its internal transcript distribution Q_h = E_Z[p_{h+Z}]."

Parameter ranges (§6, p.25: "We use the parameter ranges of Theorem 2 throughout this section"):
`N ≥ 1`, `d ≥ 2`, `k ≥ 1`, `0 < ε ≤ 1`, `0 < β < 1/2`, and a query table in `[0,1]^{k×d}`.

**Formalization Note.** Pure `ε`-DP under record replacement is Definition 4 with `δ = 0`
(`IsDP N d · ε 0`). Algorithm 2's output law is `alg2Law` (the law of `p̂ = D(y)`, on `ℝ^d` with
the Borel σ-algebra) and its internal transcript law is `transcriptLaw` (`∑_y Q_h(y) δ_y` on the
finite discrete space `[K]^T`, so every set of transcripts is an event). -/
theorem proposition_22 (N d k : ℕ) (ε β : ℝ) (hN : 1 ≤ N) (hd : 2 ≤ d) (hk : 1 ≤ k)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hβ : 0 < β) (hβ2 : β < 1 / 2) (Q : Fin k → Fin d → ℝ)
    (hQ : ∀ i j, Q i j ∈ Set.Icc (0 : ℝ) 1) :
    IsDP N d (alg2Law N d k ε β Q) ε 0 ∧ IsDP N d (transcriptLaw N d k ε β Q) ε 0 := by sorry

end PureDPQR
