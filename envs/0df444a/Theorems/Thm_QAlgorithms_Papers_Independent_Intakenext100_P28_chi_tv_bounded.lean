-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_chi_tv_bounded
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.chi_tv_bounded
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:44:15.773298+00:00
-- url     : https://prove2.me/theorems/71ada76f-cdfb-40b1-bf40-bd0df1d46152
-- title:
--   Example 6: bounded-density chi-square/TV bound (171)
-- statement:
--   For probability measures with essential density parameters $\beta_1,\beta_2$,
--
--   $$\chi^2(P\|Q)\le\max\{\beta_1^{-1}-1,1-\beta_2\}|P-Q|.$$
--
--   Here $\beta_1^{-1}=+\infty$ when $\beta_1=0$; the bound is finite when $\beta_1>0$. Extended divergences handle non-AC pairs. This is the explicit application (171).
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 25, Example 6

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Example 6: bounded-rnDensityReal chiSquareDiv-square/TV bound (171). Sason--Verdu, arXiv:1508.00335v7, PDF p.25.  -/
theorem chi_tv_bounded
    {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    chiSquareDiv P Q ≤ max (upperDensity P Q - 1) (ENNReal.ofReal (1 - inverseUpperDensity Q P)) * fullVariation P Q := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
