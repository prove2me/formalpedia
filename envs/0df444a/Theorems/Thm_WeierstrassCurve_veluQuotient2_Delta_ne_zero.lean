-- Prove2me | Theorems.Thm_WeierstrassCurve_veluQuotient2_Delta_ne_zero
-- name    : WeierstrassCurve.veluQuotient2_Delta_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/4a9ddef2-6abc-5f7f-ada6-32fff611524b
-- title:
--   Nonvanishing discriminant of the order-two Vélu quotient
-- statement:
--   Let $R$ be a commutative ring without zero divisors, let $W$ be a Weierstrass curve over $R$ with coefficients $a_1,a_2,a_3,a_4,a_6$, and let $x_0,y_0\in R$. Write $g_x=3x_0^2+2a_2x_0+a_4-a_1y_0$ and $g_y=-(2y_0+a_1x_0+a_3)$ for the two partial derivative expressions `W.veluGx` and `W.veluGy` at $(x_0,y_0)$. Assume: the discriminant $\Delta$ of $W$ is nonzero; the pair $(x_0,y_0)$ satisfies the affine Weierstrass equation of $W$; and $g_y=0$, i.e. $2y_0+a_1x_0+a_3=0$, so that $(x_0,y_0)$ is a point of order dividing $2$. The conclusion is that the Weierstrass curve `W.veluQuotient2 x₀ y₀`, defined as the curve with the same $a_1,a_2,a_3$, with fourth coefficient $a_4-5g_x$ and sixth coefficient $a_6-b_2g_x-7x_0g_x$ (where $b_2=a_1^2+4a_2$), also has nonzero discriminant.
--
--   This is the case of kernel of order two of the statement that the quotient of an elliptic curve by a finite subgroup scheme is again elliptic: the explicit Vélu target model attached to a $2$-torsion point of a nonsingular Weierstrass curve is itself nonsingular. It discharges the nonsingularity hypothesis needed to construct the order-two Vélu isogeny and its induced map on points, and is used in the study of the modular polynomial and of rational isogenies.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_veluQuotient2_Delta_ne_zero.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_VeluOrderTwo

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace WeierstrassCurve
variable {R : Type*} [CommRing R] [NoZeroDivisors R] {W : WeierstrassCurve R} {x₀ y₀ : R}
open Affine

theorem veluQuotient2_Delta_ne_zero (hΔ : W.Δ ≠ 0)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) :
    (W.veluQuotient2 x₀ y₀).Δ ≠ 0 := by sorry
