-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_two_moment_continuous_optimum
-- name    : QAlgorithms.Papers.Independent.Information100.P19.two_moment_continuous_optimum
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:57:04.210508+00:00
-- url     : https://prove2.me/theorems/cdb1820b-221a-4f82-9e47-a8e1202e1bea
-- title:
--   Theorem 5.9
-- statement:
--   For $0<r_2\le r_1$, including $r_1>1$,
--   $$\alpha_c(r_1,r_2)=\frac{r_1^{3/2}}{\sqrt{r_2}}.$$
--   The finite measure $(r_1^2/r_2)\delta_{\sqrt{r_2/r_1}}$ is feasible and attains the value. Its atom is in $[0,1]$, but its mass need not be integral.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 33, Theorem 5.9

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Theorem 5.9; arXiv:2609.29471v1, PDF pp.33. -/
theorem two_moment_continuous_optimum (r1 r2 : ℝ) (h2 : 0<r2) (hle : r2≤r1) :
    alphaC ![r1,r2] = ENNReal.ofReal (r1*Real.sqrt r1/Real.sqrt r2) ∧
    continuousFeasible ![r1,r2]
      (ENNReal.ofReal (r1^2/r2) • Measure.dirac (Real.sqrt (r2/r1))) ∧
    ENNReal.ofReal (∫ x, x ∂(ENNReal.ofReal (r1^2/r2) •
      Measure.dirac (Real.sqrt (r2/r1)))) = alphaC ![r1,r2] := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
