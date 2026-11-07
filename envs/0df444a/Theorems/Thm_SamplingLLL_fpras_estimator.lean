-- Prove2me | Theorems.Thm_SamplingLLL_fpras_estimator
-- name    : SamplingLLL.fpras_estimator
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:59:06.527662+00:00
-- url     : https://prove2.me/theorems/44a9285d-e813-4b72-b3aa-eb79291b52d6
-- title:
--   Proof of Theorem 5.1, p.25 — the estimator
-- statement:
--   Let $m\ge1$, $0<\varepsilon\le1$, $B_i\in(0,1)$, $s_i=1-B_i$, $r_i\in[0,B_i]$, and for each $i$ let $Y_{i,k}$ be independent with $|Y_{i,k}|\le B_i$ and mean $r_i$. If $N_i$ is at least $1$ and at least
--   $$
--   \frac{32B_i^2m^2}{\varepsilon^2s_i^2}\log(16m),
--   $$
--   and $\hat r_i$ is the average of $N_i$ copies clipped to $[0,B_i]$, then, with probability at least $7/8$, $\prod_i(1-\hat r_i)$ has relative error below $\varepsilon/2$ against $\prod_i(1-r_i)$.
--
--   Differences from the source:
--   - generalization: $N_i$ equal to $\max(1,32B_i^2m^2/(\varepsilon^2s_i^2)\log(16m))$, independent copies → any integer $N_i$ at least this number, with independence only within each $i$; reason: the paper's count and independence are a special case
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), proof of Theorem 5.1, p.25

import Mathlib
import Definitions.Def_SamplingLLL_ExecAnalysis

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace SamplingLLL

/-- The FPRAS estimator in the proof of Theorem 5.1, p.25. From `N_i` independent copies of `Y_i ∈ [-B_i, B_i]`
with mean `r_i ∈ [0, B_i]` and `B_i < 1`, the clipped averages `r̂_i` give a product `∏(1 - r̂_i)` of relative
error below `ε/2` against `∏(1 - r_i)`, with probability at least `7/8`, for every `0 < ε ≤ 1`.

Source: Achlioptas, STOC 2027 submission (manuscript sha256 7a943167…), proof of Theorem 5.1, p.25.

**Formalization Note.** `N_i` is any integer at least the paper's real number
`max(1, 32 B_i² m² / (ε² s_i²) · log(16m))`, which covers the count used by `copies`. Independence is needed
only within one `i`, by the union bound in the proof. -/
theorem fpras_estimator {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : ℕ} (hm : 1 ≤ m) (B r : Fin m → ℝ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hB0 : ∀ i, 0 < B i) (hB1 : ∀ i, B i < 1) (hr0 : ∀ i, 0 ≤ r i) (hrB : ∀ i, r i ≤ B i)
    (N : Fin m → ℕ) (hN1 : ∀ i, 1 ≤ N i)
    (hN : ∀ i, 32 * B i ^ 2 * (m : ℝ) ^ 2 / (ε ^ 2 * (1 - B i) ^ 2) * Real.log (16 * m) ≤ N i)
    (Y : Fin m → ℕ → Ω → ℝ) (hYm : ∀ i k, Measurable (Y i k))
    (hYi : ∀ i, iIndepFun (Y i) μ)
    (hYB : ∀ i k ω, |Y i k ω| ≤ B i) (hYE : ∀ i k, ∫ ω, Y i k ω ∂μ = r i) :
    let rhat : Fin m → Ω → ℝ := fun i ω =>
      max 0 (min (B i) ((∑ k ∈ Finset.range (N i), Y i k ω) / (N i : ℝ)))
    ENNReal.ofReal (7 / 8) ≤
      μ {ω | |∏ i, (1 - rhat i ω) - ∏ i, (1 - r i)| < ε / 2 * ∏ i, (1 - r i)} := by sorry

end SamplingLLL
