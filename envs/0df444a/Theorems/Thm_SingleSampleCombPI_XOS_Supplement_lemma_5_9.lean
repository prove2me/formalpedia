-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_Supplement_lemma_5_9
-- name    : SingleSampleCombPI.XOS.Supplement.lemma_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:50:34.440458+00:00
-- url     : https://prove2.me/theorems/940b42c4-05f1-4f5b-99c4-ccee366d10d9
-- title:
--   Lemma 5.9 (corrected: supremal benchmark) — Finite-grid welfare bound and convergence
-- statement:
--   Fix $n$ normalized nonnegative monotone concave scalar valuations. For every integer $M\ge1$, the grid benchmark satisfies
--   $$\mathrm{Opt}_M(r)\ge\frac{M}{M+n}\mathrm{Opt}(r).$$
--   For fixed $n$ and $r$, $\mathrm{Opt}_M(r)\to\mathrm{Opt}(r)$ as $M\to\infty$. The grid benchmark ranges over all feasible $1/M$ allocations and the continuous benchmark over all feasible real allocations, including instances whose supremum is not attained.
--
--   Differences from the source:
--   - correction: an attained divisible optimum in the benchmark and rounding proof → supremal continuous benchmark, with the unchanged finite-grid maximum; reason: v₁(0)=0, v₁(x)=1 for x>0 and v₂(x)=x are admissible; their welfare supremum is 2 but no feasible allocation attains it; rounding arbitrary feasible allocations and taking suprema retains the full inequality
--   - encoding: arbitrary normalized monotone concave scalar valuations → native scalar policies and the full feasible/grid benchmarks; reason: no supporting-price oracle, differentiability or continuity at zero is added; real functions are evaluated only on [0,1]
--   - encoding: convergence as the integer grid grows → Tendsto along atTop to the continuous benchmark; reason: the irrelevant value at M=0 cannot change the limit; the quantitative inequality requires M≥1
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), Lemma 5.9, printed p. 32 / PDF p. 34; proof printed 43 / PDF 45.

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Supplement_Scalar

open scoped ENNReal

namespace SingleSampleCombPI.XOS.Supplement

/-- Lemma 5.9, PDF 34 / printed 32; proof PDF 45. The supremal
benchmark corrects the nonattained optimum in the printed rounding proof. -/
theorem lemma_5_9 {n : ℕ} (r : Fin n → Scalar) (hr : ∀ i, ScalarValid (r i)) :
    (∀ M : ℕ, 1 ≤ M → (M:ℝ)/(M+n) * scalarOpt r ≤ scalarGridOpt M r) ∧
    Filter.Tendsto (fun M : ℕ => scalarGridOpt M r) Filter.atTop (nhds (scalarOpt r)) := by sorry

end SingleSampleCombPI.XOS.Supplement
