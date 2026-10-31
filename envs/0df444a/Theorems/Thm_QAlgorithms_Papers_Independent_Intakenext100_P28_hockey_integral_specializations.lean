-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_hockey_integral_specializations
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.hockey_integral_specializations
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:51:26.061431+00:00
-- url     : https://prove2.me/theorems/df7ee693-1546-440d-9f55-5a7e5cf1e14b
-- title:
--   KL, Hellinger and chi-square integral formulas (428)–(430)
-- statement:
--   For mutually absolutely continuous probability pairs,
--
--   $$D=\log_b e\int_1^\infty[\gamma^{-1}E_\gamma(P\|Q)+\gamma^{-2}E_\gamma(Q\|P)]d\gamma,$$
--
--   $$H_\alpha=\alpha\int_1^\infty[\gamma^{\alpha-2}E_\gamma(P\|Q)+\gamma^{-\alpha-1}E_\gamma(Q\|P)]d\gamma\quad(\alpha>0,\alpha\ne1),$$
--
--   and $\chi^2(P\|Q)=2\int_1^\infty[E_\gamma(P\|Q)+\gamma^{-3}E_\gamma(Q\|P)]d\gamma$. All integrals are nonnegative extended integrals, preserving infinite divergences and every specialization (428)–(430).
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 60, KL, Hellinger and chi-square integral formulas (428)–(430)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- KL, Hellinger and chiSquareDiv-square integral formulas (428)–(430). Sason--Verdu, arXiv:1508.00335v7, PDF p.60.  -/
theorem hockey_integral_specializations
    (b : LogBase) {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ≪ Q) (hQP : Q ≪ P) :
    kl b P Q = ENNReal.ofReal (logBaseE b) *
      (∫⁻ g in Ici (1 : ℝ), ENNReal.ofReal g⁻¹ * hockey g P Q +
        ENNReal.ofReal (g ^ (-2 : ℤ)) * hockey g Q P) ∧
    (∀ a : ℝ, 0 < a → a ≠ 1 → hellinger a P Q = ENNReal.ofReal a *
      (∫⁻ g in Ici (1 : ℝ), ENNReal.ofReal (Real.rpow g (a - 2)) * hockey g P Q +
        ENNReal.ofReal (Real.rpow g (-a - 1)) * hockey g Q P)) ∧
    chiSquareDiv P Q = 2 * (∫⁻ g in Ici (1 : ℝ), hockey g P Q +
      ENNReal.ofReal (g ^ (-3 : ℤ)) * hockey g Q P) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
