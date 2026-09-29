-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_evalEval_phi
-- name    : WeierstrassCurve.Affine.evalEval_phi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/9108cbe9-4ffc-558b-8909-4bfe44ad8131
-- title:
--   Division polynomial φₙ evaluates to Φₙ(x) on the curve
-- statement:
--   Let $R$ be a commutative ring and let $W$ be a Weierstrass curve over $R$, with coefficients $a_1,a_2,a_3,a_4,a_6$. Let $x,y \in R$ be a pair satisfying the affine Weierstrass equation of $W$, i.e. $y^2 + a_1xy + a_3y - (x^3 + a_2x^2 + a_4x + a_6) = 0$, which is Mathlib's `W.toAffine.Equation x y`. Then for every integer $n$ the bivariate division polynomial $\phi_n \in R[x][y]$ attached to $W$, evaluated at $(x,y)$ (first in $y$, then in $x$, as `evalEval` prescribes), agrees with the value at $x$ of the univariate polynomial $\Phi_n \in R[x]$ attached to $W$: $\phi_n(x,y) = \Phi_n(x)$. No invertibility, reducedness or integrality hypothesis on $R$ is imposed, and no hypothesis that $(x,y)$ be a nonsingular point; the only constraint on the pair $(x,y)$ is the Weierstrass equation itself.
--
--   This is the pointwise form, at a point of the affine curve, of the congruence $\phi_n \equiv \Phi_n$ modulo the Weierstrass polynomial in the coordinate ring of $W$; it is what allows the $x$-coordinate of $nP$ to be computed by the univariate quotient $\Phi_n/\Psi_n^2$. It is used in the treatment of torsion points and of the modular-curve computations that invoke division polynomials, in particular in the lemmas producing roots of $\Psi$-type polynomials from relations $Q = n \cdot P$ between points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_evalEval_phi.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.Affine.evalEval_phi {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R} (h : W.toAffine.Equation x y) (n : ℤ) : (W.φ n).evalEval x y = (W.Φ n).eval x := by sorry
