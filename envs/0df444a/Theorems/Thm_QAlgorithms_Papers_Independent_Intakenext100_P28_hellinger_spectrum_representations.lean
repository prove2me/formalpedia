-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_hellinger_spectrum_representations
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.hellinger_spectrum_representations
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:48:20.920758+00:00
-- url     : https://prove2.me/theorems/48f368e4-cafe-4153-bd86-2b5b2cc44cb3
-- title:
--   Corollary 6: Hellinger representations (480)–(483) obtained by the exact transform of all four Renyi representations
-- statement:
--   With $P\ll Q$, $\alpha>0$, $\alpha\ne1$, and $F,\zeta$ as in Theorem 35,
--
--   $$\begin{aligned}
--   H_\alpha&=\frac{\beta_1^{1-\alpha}-1}{\alpha-1}-\int_{\beta_2}^{\beta_1^{-1}}t^{\alpha-2}F(t)dt&& (\beta_1>0),\\
--   &=\frac1{1-\alpha}-\int_{\beta_2}^\infty t^{\alpha-2}F(t)dt&& (\beta_1=0,\alpha<1),\\
--   &=\int_0^\infty\zeta(t)dt-\frac1{\alpha-1}&& (\alpha>1),\\
--   &=\frac{\beta_2^{\alpha-1}-1}{\alpha-1}+\int_{\beta_2}^\infty\zeta(t)dt&& (\alpha>1).
--   \end{aligned}$$
--
--   These are all four transforms (480)–(483). Their finite subtractions and nonnegative extended integrals are well-defined even when Hellinger divergence is infinite.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 67, Corollary 6

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Corollary 6: Hellinger representations (480)–(483) obtained by the exact transform of all four Renyi representations. Sason--Verdu, arXiv:1508.00335v7, PDF p.67.  -/
theorem hellinger_spectrum_representations
    (b : LogBase) (a : ℝ) (ha : 0 < a ∧ a ≠ 1)
    {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ≪ Q) :
    (0 < inverseUpperDensity P Q → (hellinger a P Q : EReal) =
      ((Real.rpow (inverseUpperDensity P Q) (1 - a) - 1) / (a - 1) : ℝ) -
        (cdfMoment b a P Q (ENNReal.ofReal (inverseUpperDensity Q P)) (upperDensity P Q) : EReal)) ∧
    (inverseUpperDensity P Q = 0 → a < 1 → (hellinger a P Q : EReal) =
      (1 / (1 - a) : ℝ) - (cdfMoment b a P Q (ENNReal.ofReal (inverseUpperDensity Q P)) ∞ : EReal)) ∧
    (1 < a → (hellinger a P Q : EReal) =
      (tailMoment b a P Q 0 ∞ : EReal) - (1 / (a - 1) : ℝ) ∧
      (hellinger a P Q : EReal) =
        ((Real.rpow (inverseUpperDensity Q P) (a - 1) - 1) / (a - 1) : ℝ) +
        (tailMoment b a P Q (ENNReal.ofReal (inverseUpperDensity Q P)) ∞ : EReal)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
