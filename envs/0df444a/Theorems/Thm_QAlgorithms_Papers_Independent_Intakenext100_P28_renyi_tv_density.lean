-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_renyi_tv_density
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.renyi_tv_density
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:49:04.73637+00:00
-- url     : https://prove2.me/theorems/a1e00b01-1148-4cdb-91c6-9eead8ac38d6
-- title:
--   Theorem 37: D_alpha<=log(1+(TV/2)*(beta1^(1-alpha)-1)/(1-beta1))/(alpha-1)
-- statement:
--   If $0<\beta_1<1$ and $\alpha>0$, $\alpha\ne1$, then
--
--   $$D_\alpha(P\|Q)\le\frac1{\alpha-1}\log_b\left(1+
--   \frac{|P-Q|}{2}\frac{\beta_1^{1-\alpha}-1}{1-\beta_1}\right).$$
--
--   Positive $\beta_1$ supplies absolute continuity and bounded density. For $\alpha<1$ the logarithm argument is positive on the actual admissible total-variation range.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 69, Theorem 37

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 37: D_alpha<=log(1+(TV/2)*(beta1^(1-alpha)-1)/(1-beta1))/(alpha-1). Sason--Verdu, arXiv:1508.00335v7, PDF p.69.  -/
theorem renyi_tv_density
    (b : LogBase) (a : ℝ) (ha : 0 < a ∧ a ≠ 1)
    {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hb : 0 < inverseUpperDensity P Q ∧ inverseUpperDensity P Q < 1) :
    renyiDiv b a P Q ≤ (logB b (1 + (fullVariation P Q).toReal / 2 *
      (Real.rpow (inverseUpperDensity P Q) (1 - a) - 1) / (1 - inverseUpperDensity P Q)) / (a - 1) : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
