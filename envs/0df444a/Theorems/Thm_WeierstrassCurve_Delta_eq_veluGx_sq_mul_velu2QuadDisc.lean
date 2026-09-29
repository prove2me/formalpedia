-- Prove2me | Theorems.Thm_WeierstrassCurve_Delta_eq_veluGx_sq_mul_velu2QuadDisc
-- name    : WeierstrassCurve.Delta_eq_veluGx_sq_mul_velu2QuadDisc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/588c210e-7262-5687-86db-d00cd5491399
-- title:
--   Δ = gₓ(Q)² d(x₀) at a 2-torsion point
-- statement:
--   Let $R$ be a commutative ring and $W$ a Weierstrass curve over $R$ with coefficients $a_1,a_2,a_3,a_4,a_6$, and let $x_0,y_0 \in R$. Assume two hypotheses: first, that $(x_0,y_0)$ lies on the associated affine curve, i.e. it satisfies the Weierstrass equation $y_0^2 + a_1 x_0 y_0 + a_3 y_0 = x_0^3 + a_2 x_0^2 + a_4 x_0 + a_6$; second, that `W.veluGy x₀ y₀`, which by definition is $-(2y_0 + a_1 x_0 + a_3)$, vanishes — so the point is a $2$-torsion point in the sense that the partial derivative in $y$ of the Weierstrass polynomial vanishes at it. Under these hypotheses the discriminant of $W$ factors as
--   $$\Delta = \bigl(3x_0^2 + 2a_2 x_0 + a_4 - a_1 y_0\bigr)^2 \cdot \bigl(b_2^2 - 8 b_2 x_0 - 48 x_0^2 - 32 b_4\bigr),$$
--   where the first factor is `W.veluGx x₀ y₀` (the negative of the partial derivative in $x$) and the second is `W.velu2QuadDisc x₀`, with $b_2 = a_1^2 + 4a_2$ and $b_4 = 2a_4 + a_1 a_3$ the usual Weierstrass quantities. No invertibility, reducedness or nondegeneracy assumption is imposed: the assertion is an identity in $R$.
--
--   The identity expresses the classical factorisation of the discriminant at a $2$-torsion point, in the form $\operatorname{disc}((X-x_0)Q) = \operatorname{Res}(X-x_0,Q)^2 \operatorname{disc}(Q)$ applied to the splitting off of the root $x_0$ from the $2$-division polynomial. It is used to show that both factors are nonzero at a $2$-torsion point when $\Delta$ is, in [`WeierstrassCurve.veluGx_ne_zero_of_two_torsion`](thm.html#WeierstrassCurve.veluGx_ne_zero_of_two_torsion) and [`WeierstrassCurve.velu2QuadDisc_ne_zero_of_two_torsion`](thm.html#WeierstrassCurve.velu2QuadDisc_ne_zero_of_two_torsion), which feed into the construction of the quotient of a curve by an order-two subgroup via Vélu's formulae.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Delta_eq_veluGx_sq_mul_velu2QuadDisc.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_VeluOrderTwo

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace WeierstrassCurve
variable {R : Type*} [CommRing R] {W : WeierstrassCurve R}
open Affine

theorem Delta_eq_veluGx_sq_mul_velu2QuadDisc {x₀ y₀ : R}
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) :
    W.Δ = W.veluGx x₀ y₀ ^ 2 * W.velu2QuadDisc x₀ := by sorry
