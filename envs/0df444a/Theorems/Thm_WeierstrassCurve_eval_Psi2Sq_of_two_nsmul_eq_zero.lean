-- Prove2me | Theorems.Thm_WeierstrassCurve_eval_Psi2Sq_of_two_nsmul_eq_zero
-- name    : WeierstrassCurve.eval_Psi2Sq_of_two_nsmul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/11c37aaa-5ef0-5469-bc0b-d3443d29ab92
-- title:
--   x-coordinates of 2-torsion points are roots of Ψ₂²
-- statement:
--   Let $F$ be a field and let $W$ be an affine Weierstrass curve over $F$, given by $y^2 + a_1xy + a_3y = x^3 + a_2x^2 + a_4x + a_6$. Let $x, y \in F$ be such that the pair $(x,y)$ is a nonsingular point of $W$, that is, it satisfies the Weierstrass equation and the two partial derivatives of the defining polynomial do not both vanish at it; write $(x,y)$ for the corresponding element `Affine.Point.some` of the group $W$.`Point` of points of $W$. Assume that twice this point is the identity of $W$.`Point`, i.e.\ that $(x,y)$ is a point of order dividing $2$. The conclusion is that $x$ is a root of the $2$-division polynomial $\Psi_2^2 = 4X^3 + b_2X^2 + 2b_4X + b_6$ attached to $W$, in the sense that its evaluation at $x$ is $0$.
--
--   This is one direction of the classical description of $2$-torsion on a Weierstrass curve: every affine point killed by $2$ has abscissa among the roots of the $2$-torsion cubic, valid in every characteristic. It is used in the count of the $2$-torsion subgroup, [`WeierstrassCurve.card_torsionBy_two_eq_card_option_Psi2Sq_roots`](thm.html#WeierstrassCurve.card_torsionBy_two_eq_card_option_Psi2Sq_roots), and in [`WeierstrassCurve.isTwoKernel_X_sub_C_coordsOrZero_of_addOrderOf_eq_two`](thm.html#WeierstrassCurve.isTwoKernel_X_sub_C_coordsOrZero_of_addOrderOf_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_eval_Psi2Sq_of_two_nsmul_eq_zero.lean

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace WeierstrassCurve

theorem eval_Psi2Sq_of_two_nsmul_eq_zero {F : Type*} [Field F] [DecidableEq F]
    {W : WeierstrassCurve.Affine F} {x y : F} (h : W.Nonsingular x y)
    (h2 : 2 • (Affine.Point.some _ _ h : W.Point) = 0) : W.Ψ₂Sq.eval x = 0 := by sorry
