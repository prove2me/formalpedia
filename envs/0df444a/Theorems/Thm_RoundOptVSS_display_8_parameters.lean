-- Prove2me | Theorems.Thm_RoundOptVSS_display_8_parameters
-- name    : RoundOptVSS.display_8_parameters
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:01:26.01859+00:00
-- url     : https://prove2.me/theorems/fc8d78e1-4b65-4a8f-92a2-f88170e8cd09
-- title:
--   Display (8) — the parameters of §8.4 give total error at most $2^{-\kappa}$
-- statement:
--   **Display (8)** (§8.4). Let $q=|\mathbb F|$ and suppose $q>2(h_{\max}+1)$ and $q\ge2^{\kappa+1}Nn(\delta_{\max}+1)$. Then the checking-point domain bound satisfies $q-h_{\max}-1>q/2$, and
--
--   $$Nn\Big(\frac1{q-1}+\frac{\delta_{\max}}{q-h_{\max}-1}\Big)\le2^{-\kappa}.$$
--
--   With $N$ the total number of labels, every label's error $1/(q-1)+\delta_L/|\mathcal A_L|$ is at most the bracket, so the union bound of Lemma 8.3 is at most $2^{-\kappa}$; this is the error of the main theorem.
--
--   Differences from the source:
--   - generalization: N = (n + 1)M, h_max = max{h, m}, δ_max = h_max + t − 1 → arbitrary natural numbers N, n, κ, h_max, δ_max, q; reason: the inequality holds for all of them; the paper's values are a special case
--   - encoding: |𝔽| → q : ℕ with real arithmetic; reason: same numbers
-- source:
--   Liu-Zhang, Masserova, Round-Optimal Statistical Verifiable Secret Sharing with Polynomial Complexity, manuscript (2026; STOC 2027 submission, sha256 3a45d95d…), display (8), §8.4 (p.31)

import Mathlib

namespace RoundOptVSS

/-- **Display (8)**, §8.4, p.31 of Liu-Zhang, Masserova, *Round-Optimal Statistical Verifiable
Secret Sharing with Polynomial Complexity*, manuscript (STOC 2027 submission, sha256
3a45d95d…): if the base field has `q = |𝔽|` elements with `q > 2(h_max + 1)` and
`q ≥ 2^{κ+1} N n (δ_max + 1)`, then the checking-point domain size bound satisfies
`q − h_max − 1 > q/2` and
`N n (1/(q − 1) + δ_max/(q − h_max − 1)) ≤ 2^{−κ}`.

**Formalization Note.** The arithmetic is in `ℝ`; `N, n, κ, h_max, δ_max, q` are arbitrary
natural numbers (in the paper `N = (n + 1)M`, `h_max = max{h, m}`, `δ_max = h_max + t − 1`). -/
theorem display_8_parameters (N n κ hmax δmax q : ℕ) (hq1 : 2 * (hmax + 1) < q)
    (hq2 : 2 ^ (κ + 1) * N * n * (δmax + 1) ≤ q) :
    (q : ℝ) / 2 < (q : ℝ) - hmax - 1 ∧
    (N : ℝ) * n * (1 / ((q : ℝ) - 1) + δmax / ((q : ℝ) - hmax - 1)) ≤ (2 : ℝ) ^ (-(κ : ℤ)) := by sorry

end RoundOptVSS
