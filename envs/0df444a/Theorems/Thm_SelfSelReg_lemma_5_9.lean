-- Prove2me | Theorems.Thm_SelfSelReg_lemma_5_9
-- name    : SelfSelReg.lemma_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:48:27.912057+00:00
-- url     : https://prove2.me/theorems/7513b410-8fd3-4435-9292-4950679d20d7
-- title:
--   Lemma 5.9 — weights across degrees $\big|\log\frac{\lambda_j^{(2r)}/\lambda_i^{(2r)}}{\lambda_j^{(2s)}/\lambda_i^{(2s)}}\big|\le(s-r)\log K$
-- statement:
--   In the Gaussian self-selection model ($n\ge1$, $2\le k\le n$) under Assumption 1.2 with constants $B\ge1$, $\Delta\in(0,1]$, let $K,T,s$ be the hyperparameters of Hyperparameters 4.1. For every $i,j\in[k]$ and $1\le r\le s$,
--   $$\Big|\log\frac{\lambda_j^{(2r)}/\lambda_i^{(2r)}}{\lambda_j^{(2s)}/\lambda_i^{(2s)}}\Big|\le(s-r)\log K .$$
--
--   The relative weight of two components changes by at most a factor $K^{s-r}$ between degrees $2r$ and $2s$; this bounds the effect of the intermediate projections on the final even moment.
--
--   **Formalization Note** Natural logarithm. The weights are positive (Lemma 5.7), so the logarithm is of a positive number.
--
--   Differences from the source:
--   - reading: s := K⁴ log n (9), printed as a real number → s = ⌈K⁴ log n⌉ (hypS), natural logarithm; reason: s is used as a tensor order ("let s ≥ 1 be an integer", Lemmas 5.7, 5.8) and (182) states s ≤ 2K⁴ log n, which presupposes rounding up; the ceiling is also the stronger choice for every bound that improves with s
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Lemma 5.9, p.25 (PDF p.28)

import Mathlib
import Definitions.Def_SelfSelReg_SatisfiesAssumption
import Definitions.Def_SelfSelReg_hypK
import Definitions.Def_SelfSelReg_restrictedMoment

namespace SelfSelReg

/-- **Lemma 5.9** (Weights Across Degrees).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Lemma 5.9, p.25 (PDF p.28): "Consider the Gaussian self-selection model
(Definition 1.1) under the boundedness and uncoveredness assumptions (Assumption 1.2). Use the
hyperparameters K, T, s from Hyperparameters 4.1. For every i, j ∈ [k] and 1 ≤ r ≤ s,
|log((λ_j^{(2r)}/λ_i^{(2r)}) / (λ_j^{(2s)}/λ_i^{(2s)}))| ≤ (s − r) log K."

**Formalization Note.** `K = hypK B ∆`, `s = hypS B ∆ n = ⌈K⁴ log n⌉`, `T = hypT B ∆ n`;
`λ_i^{(2r)} = weight w T i r`. Natural logarithm. The weights are positive (Lemma 5.7), so the
logarithm is of a positive number. -/
theorem lemma_5_9 (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n) (B Δ : ℝ) (hB : 1 ≤ B)
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (w : Fin k → EuclideanSpace ℝ (Fin n))
    (hw : SatisfiesAssumption B Δ w) (i j : Fin k) (r : ℕ) (hr : 1 ≤ r)
    (hrs : r ≤ hypS B Δ n) :
    |Real.log ((weight w (hypT B Δ n) j r / weight w (hypT B Δ n) i r) /
        (weight w (hypT B Δ n) j (hypS B Δ n) / weight w (hypT B Δ n) i (hypS B Δ n)))| ≤
      ((hypS B Δ n : ℝ) - r) * Real.log (hypK B Δ) := by sorry

end SelfSelReg
