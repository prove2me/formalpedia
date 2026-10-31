-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_hellinger_tv_density
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.hellinger_tv_density
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:49:24.897964+00:00
-- url     : https://prove2.me/theorems/24b1e7ac-d42d-4dd2-bd89-fe650362a153
-- title:
--   Corollary 7: H_alpha<=[(beta1^(1-alpha)-1)/(2(alpha-1)(1-beta1))] TV
-- statement:
--   For $0<\beta_1<1$ and $\alpha>0$, $\alpha\ne1$,
--
--   $$H_\alpha(P\|Q)\le
--   \frac{\beta_1^{1-\alpha}-1}{2(\alpha-1)(1-\beta_1)}|P-Q|.$$
--
--   This is the exact Hellinger transform of the Renyi bound, with its full parameter domain.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 70, Corollary 7

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Corollary 7: H_alpha<=[(beta1^(1-alpha)-1)/(2(alpha-1)(1-beta1))] TV. Sason--Verdu, arXiv:1508.00335v7, PDF p.70.  -/
theorem hellinger_tv_density
    (a : ℝ) (ha : 0 < a ∧ a ≠ 1)
    {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hb : 0 < inverseUpperDensity P Q ∧ inverseUpperDensity P Q < 1) :
    hellinger a P Q ≤ ENNReal.ofReal ((Real.rpow (inverseUpperDensity P Q) (1 - a) - 1) /
      (2 * (a - 1) * (1 - inverseUpperDensity P Q))) * fullVariation P Q := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
