-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P22_theta_inversion
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P22.theta_inversion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:48:09.968999+00:00
-- url     : https://prove2.me/theorems/9234d30c-286c-435b-b7ac-a423cb077938
-- title:
--   Characteristic theta inversion with the analytic Gaussian branch
-- statement:
--   Let $g\ge1$ and let $T$ be a symmetric complex $g\times g$ matrix with positive definite imaginary part. For complex vectors $a,b,z\in\mathbb C^g$, define the Riemann–Siegel theta function by the absolutely convergent series
--   $$\Theta[a;b](z\mid T)=\sum_{m\in\mathbb Z^g}\exp\{i\pi(m+a)^tT(m+a)+2\pi i(m+a)^t(z+b)\}.$$
--   Let $G(T)=\int_{\mathbb R^g}\exp(i\pi y^tTy)\,dy$. This integral is integrable and fixes the analytic branch $G(T)=\det(-iT)^{-1/2}$ continuously from $T=iY$ with $Y$ positive definite. Then
--   $$G(T)^2\det(-iT)=1,\qquad
--   \Theta[a;b](z\mid T)=e^{2\pi i a^t(z+b)}G(T)\Theta[z+b;-a](0\mid -T^{-1}).$$
--   Both the theta series and the series of absolute values converge. This identity supplies the general theta transformation used in the crossing calculation; it does not assume or assert physical crossing symmetry.
-- source:
--   Entanglement entropy of two disjoint intervals in conformal field theory II, arXiv:1011.5482v1, PDF p. 12, §4.1, equation (53)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P22

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P22

open scoped BigOperators Topology

open Filter MeasureTheory

/-- PDF pp. 12–13, (53), with arbitrary complex characteristics and argument.
The Gaussian integral realizes the source's analytic determinant branch.
Integrability and absolute convergence are conclusions, not assumed target laws. -/
theorem theta_inversion (g : ℕ) (hg : 1 ≤ g)
    (T : Matrix (Fin g) (Fin g) ℂ) (hT : Siegel T) (a b z : Fin g → ℂ) :
    Summable (thetaSummand T a b z) ∧
    Summable (fun m => ‖thetaSummand T a b z m‖) ∧
    Integrable (fun y : Fin g → ℝ => Complex.exp (Complex.I * Real.pi *
      bilinear (fun i => (y i : ℂ)) (T.mulVec (fun i => (y i : ℂ))))) ∧
    gaussianFactor T ^ 2 * Matrix.det ((-Complex.I) • T) = 1 ∧
    characteristicTheta T a b z = Complex.exp (2 * Real.pi * Complex.I * bilinear a (z + b)) *
      gaussianFactor T * characteristicTheta (-(T⁻¹)) (z + b) (-a) 0 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P22

end
