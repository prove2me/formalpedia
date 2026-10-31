-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_fDiv_hockey_integral
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.fDiv_hockey_integral
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:40:59.435749+00:00
-- url     : https://prove2.me/theorems/678c8285-05cb-41d7-b108-4aca3cc6022a
-- title:
--   Proposition 3: Df=integral_1^infinity[f_second(gamma)E_gamma(P||Q)+gamma^{-3}f_second(gamma^{-1})E_gamma(Q||P)]dgamma
-- statement:
--   For mutually absolutely continuous probability measures, let $f$ be convex and twice differentiable on $(0,\infty)$ with $f(1)=0$. Then
--
--   $$D_f(P\|Q)=\int_1^\infty\left[f''(\gamma)E_\gamma(P\|Q)+\gamma^{-3}f''(\gamma^{-1})E_\gamma(Q\|P)\right]d\gamma.$$
--
--   Convexity makes the integrand nonnegative, so the integral may be infinite. Twice differentiability is required, without a stronger $C^2$ hypothesis. The proof attributes the underlying representation to [66, Theorem 11] and [18, Corollary 3.7].
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 59, Proposition 3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Proposition 3: Df=integral_1^infinity[f_second(gamma)E_gamma(P||Q)+gamma^{-3}f_second(gamma^{-1})E_gamma(Q||P)]dgamma. Sason--Verdu, arXiv:1508.00335v7, PDF p.59.  -/
theorem fDiv_hockey_integral
    (f : ℝ → ℝ) (hf : Generator f)
    (hd : ∀ t : ℝ, 0 < t → DifferentiableAt ℝ f t ∧ DifferentiableAt ℝ (deriv f) t)
    {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ≪ Q) (hQP : Q ≪ P) :
    fDiv f P Q = ((∫⁻ g in Ici (1 : ℝ), ENNReal.ofReal (deriv (deriv f) g) * hockey g P Q +
      ENNReal.ofReal (g ^ (-3 : ℤ) * deriv (deriv f) g⁻¹) * hockey g Q P) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
