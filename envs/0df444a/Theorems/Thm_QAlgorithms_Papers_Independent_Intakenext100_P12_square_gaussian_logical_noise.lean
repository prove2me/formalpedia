-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P12_square_gaussian_logical_noise
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P12.square_gaussian_logical_noise
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:10:07.571854+00:00
-- url     : https://prove2.me/theorems/6c2f694c-3720-46a5-ac52-a181ae541ec4
-- title:
--   §VIII (94): induced binary noise for the square code
-- statement:
--   Let $\sigma>0$ and apply independent Gaussian $N(0,\sigma^2)$ displacements to $q$ and $p$. Under ideal nearest-cell square-qubit recovery let $p_e$ be the Gaussian mass of cells whose nearest $\sqrt\pi$-multiple has odd index. The two logical Pauli bits are independent Bernoulli variables with this same parameter; explicitly their joint law is $p_e^{a+b}(1-p_e)^{2-a-b}$ for $a,b\in\{0,1\}$. Their defining integrands are integrable and $0\le p_e\le1$. Furthermore
--
--   $$p_e<\frac{2}{\sqrt{2\pi\sigma^2}}\int_{\sqrt\pi/2}^{\infty}e^{-x^2/(2\sigma^2)}\,dx.$$
--
--   The exact probability counts odd cells only, so harmless larger stabilizer shifts are retained.
-- source:
--   Encoding a qubit in an oscillator, arXiv:quant-ph/0008040v3, PDF p. 11, §VIII (94): induced binary noise for the square code

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P12

noncomputable section

open scoped BigOperators

open MeasureTheory Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

namespace QAlgorithms.Papers.Independent.Intakenext100.P12

/-- Section VIII (94), PDF p.11: independent logical binary errors and the strict tail bound.
The cutoff is sqrt(pi)/2, not sqrt(pi/2). -/
theorem square_gaussian_logical_noise (sigma : ℝ) (hs : 0 < sigma) :
    Integrable (fun x : ℝ => if squareParity x then quadratureGaussianDensity sigma x else 0) volume ∧
    (∀ a b : Bool, Integrable (fun xy : ℝ × ℝ =>
      if squareParity xy.1 = a ∧ squareParity xy.2 = b then
        quadratureGaussianDensity sigma xy.1 * quadratureGaussianDensity sigma xy.2 else 0) volume) ∧
    0 ≤ squareErrorRate sigma ∧ squareErrorRate sigma ≤ 1 ∧
    (∀ a b : Bool, squareJoint sigma a b =
      (if a then squareErrorRate sigma else 1 - squareErrorRate sigma) *
      (if b then squareErrorRate sigma else 1 - squareErrorRate sigma)) ∧
    squareErrorRate sigma <
      2 * ∫ x in Set.Ioi (Real.sqrt Real.pi / 2), quadratureGaussianDensity sigma x := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P12

end
