-- Prove2me | Theorems.Thm_WeierstrassCurve_eval_psiSq_eq_zero_of_singular
-- name    : WeierstrassCurve.eval_psiSq_eq_zero_of_singular
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/d3efae4c-b63a-5d12-9b5b-eea9c8deacce
-- title:
--   Division polynomials ψₙ² vanish at a singular point
-- statement:
--   Let $R$ be a commutative ring and let $W$ be a Weierstrass curve over $R$, with coefficients $a_1,a_2,a_3,a_4,a_6$. Let $x_0,y_0\in R$ be such that: the point $(x_0,y_0)$ satisfies the affine Weierstrass equation of $W$, i.e. $y_0^2+a_1x_0y_0+a_3y_0=x_0^3+a_2x_0^2+a_4x_0+a_6$; the partial derivative of the defining polynomial in $x$ vanishes at $(x_0,y_0)$, written here as $a_1y_0=3x_0^2+2a_2x_0+a_4$; and the partial derivative in $y$ vanishes, $2y_0+a_1x_0+a_3=0$. Thus $(x_0,y_0)$ is a singular point of the Weierstrass cubic in the scheme-theoretic sense, no invertibility or reducedness being assumed of $R$. Then for every integer $n$ whose absolute value exceeds $1$, the univariate division polynomial $\Psi^2_n\in R[X]$ of $W$ (Mathlib's `WeierstrassCurve.ΨSq`, the polynomial congruent to $\psi_n^2$) evaluates to $0$ at $x_0$.
--
--   Classically, $\psi_n^2(X)=n^2\prod_{P\in W[n]\setminus\{O\}}(X-x(P))$ for a nonsingular curve; the present statement is the degenerate counterpart, asserting that the abscissa of a singular point of a Weierstrass cubic is a root of every $\psi_n^2$ with $|n|\ge 2$. It is used in [`WeierstrassCurve.exists_torsionBy_residueChar_not_inZeroComponentAt`](thm.html#WeierstrassCurve.exists_torsionBy_residueChar_not_inZeroComponentAt), where torsion points whose reduction meets the singular point of a curve with multiplicative reduction must be located.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_eval_psiSq_eq_zero_of_singular.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve Polynomial

theorem WeierstrassCurve.eval_psiSq_eq_zero_of_singular {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x₀ y₀ : R} (he : W.toAffine.Equation x₀ y₀) (hFx : W.a₁ * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄) (hFy : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) {n : ℤ} (hn : 1 < n.natAbs) : (W.ΨSq n).eval x₀ = 0 := by sorry
