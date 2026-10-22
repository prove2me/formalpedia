-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P13_weyl_laguerre
-- name    : QAlgorithms.Papers.Independent.Gap48.P13.weyl_laguerre
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:40:28.150435+00:00
-- url     : https://prove2.me/theorems/69a4c463-0266-4546-b209-8b9f16688cc1
-- title:
--   Number-basis matrix elements of the Weyl unitary
-- statement:
--   Let $m,n\in\mathbb N$ with $m\le n$, let $z\in\mathbb C$, and let $\phi_j$ be the normalized Hermite basis. With $W(z)=\exp(za-\overline z a^+)$,
--
--   $$\langle\phi_m,W(z)\phi_n\rangle=e^{-|z|^2/2}\sqrt{\frac{m!}{n!}}\,z^{n-m}L_m^{n-m}(|z|^2).$$
--
--   For a nonnegative integer $\alpha$, the associated Laguerre polynomial here is
--
--   $$L_m^\alpha(x)=\sum_{k=0}^m\frac{(-1)^k(m+\alpha)!}{k!(m-k)!(\alpha+k)!}x^k.$$
--
--   The inner product is conjugate-linear in its first argument. This formula gives the source's stated upper-triangular branch of the Weyl matrix, with its operator realization included.
-- source:
--   Markov triplets on CCR-algebras, arXiv:0812.3724v2, PDF p. 5, Theorem 1.2

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P13

noncomputable section

open Filter MeasureTheory

open scoped BigOperators Topology ENNReal ComplexOrder Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap48.P13

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P21 (imaginaryPower)

/-- Theorem 1.2, PDF pp.5–6: only the stated n>=m branch. The erroneous
unconjugated symmetry sentence on p.6 is not used. -/
theorem weyl_laguerre (z : ℂ) (m n : ℕ) (hmn : m ≤ n) :
    (Osc.HasFockMatrix (Osc.displacement (-star z)) (Osc.displacementMatrix (-star z)) ∧
      (ContinuousLinearMap.adjoint (Osc.displacement (-star z))).comp (Osc.displacement (-star z)) = 1 ∧
      (Osc.displacement (-star z)).comp (ContinuousLinearMap.adjoint (Osc.displacement (-star z))) = 1) ∧
    inner ℂ (Osc.fockKet m) ((Osc.displacement (-star z)) (Osc.fockKet n)) =
      (Real.exp (-Complex.normSq z / 2) *
        Real.sqrt ((Nat.factorial m : ℝ) / (Nat.factorial n : ℝ)) : ℝ) *
      z ^ (n - m) * (associatedLaguerre m (n - m) (Complex.normSq z) : ℂ) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P13

end
