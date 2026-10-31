-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_cGamma_relative_approximation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.cGamma_relative_approximation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:51:43.613624+00:00
-- url     : https://prove2.me/theorems/f555db94-7f72-49cf-9a50-63760cac6d47
-- title:
--   Remark 41: proposed approximation and relative-error claims
-- statement:
--   Let $\gamma>1$, $\delta=(11791/10000)\gamma\ln\gamma$, and define
--
--   $$\widetilde c_\gamma=\frac{\delta}{(\delta+\gamma)\log_b((\delta+\gamma)/e)+\log_b e}.$$
--
--   With $c_\gamma$ the exact coefficient (434), Remark 41 asserts $|\widetilde c_\gamma/c_\gamma-1|<1/100$ for all $\gamma>1$, and at most $1/1000$ for $\gamma\ge2$. The exact denominator is $c_\gamma$, and $1.1791$ is the printed coefficient, not an optimized constant substituted by rounding.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 63, Remark 41

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Remark 41: proposed approximation and relative-error claims. Sason--Verdu, arXiv:1508.00335v7, PDF p.63.  -/
theorem cGamma_relative_approximation
    (b : LogBase) :
    (∀ g : ℝ, 1 < g → |cGammaApprox b g / hockeyKLConstant b g - 1| < (1 / 100 : ℝ)) ∧
    (∀ g : ℝ, 2 ≤ g → |cGammaApprox b g / hockeyKLConstant b g - 1| ≤ (1 / 1000 : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
