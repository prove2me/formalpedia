-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_kl_hellinger_bounds
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.kl_hellinger_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:32:56.27976+00:00
-- url     : https://prove2.me/theorems/c97a723c-83b2-4002-9aa5-6fbeeff972c9
-- title:
--   Theorem 9: For 0<alpha<1: kappa_alpha(beta2)<=D/H_alpha<=kappa_alpha(beta1^{-1}); for alpha>1 the two endpoint roles reverse
-- statement:
--   Let $P\ll Q$, $P\ne Q$, and $\alpha>0$, $\alpha\ne1$. Let $\kappa_\alpha$ be the continuous kernel (176): off $0,1,\infty$ it is $(1-\alpha)r(t)/(1-t^\alpha+\alpha t-\alpha)$; its values at 0 and 1 are $\log_b e$ and $(\log_b e)/\alpha$, and at infinity it is infinity for $\alpha<1$ and zero for $\alpha>1$. Then
--
--   $$\kappa_\alpha(\beta_2)H_\alpha\le D\le\kappa_\alpha(\beta_1^{-1})H_\alpha\quad(\alpha<1),$$
--
--   with endpoint roles reversed for $\alpha>1$. Multiplicative bounds express the intended inequalities even when both divergences are infinite.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 26, Theorem 9

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 9: For 0<alpha<1: kappa_alpha(beta2)<=D/H_alpha<=kappa_alpha(beta1^{-1}); for alpha>1 the two endpoint roles reverse. Sason--Verdu, arXiv:1508.00335v7, PDF p.26.  -/
theorem kl_hellinger_bounds
    (b : LogBase) (a : ℝ) (ha : 0 < a ∧ a ≠ 1)
    {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ≪ Q) (hne : P ≠ Q) (hb1 : inverseUpperDensity P Q < 1) (hb2 : inverseUpperDensity Q P < 1) :
    (a < 1 → entropyHellingerKernel b a (ENNReal.ofReal (inverseUpperDensity Q P)) * hellinger a P Q ≤ kl b P Q ∧
      kl b P Q ≤ entropyHellingerKernel b a (upperDensity P Q) * hellinger a P Q) ∧
    (1 < a → entropyHellingerKernel b a (upperDensity P Q) * hellinger a P Q ≤ kl b P Q ∧
      kl b P Q ≤ entropyHellingerKernel b a (ENNReal.ofReal (inverseUpperDensity Q P)) * hellinger a P Q) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
