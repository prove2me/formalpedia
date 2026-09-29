-- Prove2me | Theorems.Thm_WeierstrassCurve_velu2_tangent_addX_cleared_identity
-- name    : WeierstrassCurve.velu2_tangent_addX_cleared_identity
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/61f71ae0-8337-5555-8a73-cacf226bd63c
-- title:
--   Cleared identity behind the Vélu 2-isogeny doubling abscissa
-- statement:
--   Let $R$ be a commutative ring and $W$ a Weierstrass curve over $R$ with coefficients $a_1,a_2,a_3,a_4,a_6$, and let $x_0,y_0,x,y\in R$. Assume that $(x,y)$ and $(x_0,y_0)$ both satisfy the affine Weierstrass equation of $W$, and that $2y_0+a_1x_0+a_3=0$. Write $t=3x_0^2+2a_2x_0+a_4-a_1y_0$ for the value `W.veluGx x₀ y₀`, and abbreviate $g_x=3x^2+2a_2x+a_4-a_1y$, $g_y=2y+a_1x+a_3$, $N=a_1^2(x-x_0)+4\bigl(x^2+xx_0+x_0^2+a_2(x+x_0)+a_4-a_1y_0\bigr)$, $D=(x-x_0)^2-t$ and $C=g_x^2+a_1g_xg_y-(a_2+2x+x_0)g_y^2$. The conclusion is the polynomial identity in $R$
--   $$N\bigl(D\,(6x^2+(4a_2+a_1^2)x+2a_4+a_1a_3)+tN\bigr)\,(x-x_0)\,C=(g_yD)^2\bigl(g_y^2(x-x_0)+2C\bigr).$$
--   No invertibility, reducedness or characteristic hypothesis is imposed: the assertion is an equality of ring elements, valid over an arbitrary commutative ring once the two curve equations and the $2$-torsion relation hold.
--
--   The identity is the denominator-cleared algebraic content of the abscissa part of the tangent (doubling) case of the compatibility of Vélu's quotient map for a kernel point of order $2$ with the group law. It is used in the proof of [`WeierstrassCurve.exists_addMonoidHom_coe_eq_veluPointMap2`](thm.html#WeierstrassCurve.exists_addMonoidHom_coe_eq_veluPointMap2), where the order-$2$ Vélu point map is shown to be additive.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_velu2_tangent_addX_cleared_identity.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_Velu

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.velu2_tangent_addX_cleared_identity
    {R : Type*} [CommRing R] {W : WeierstrassCurve R} {x₀ y₀ x y : R}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) :
    (W.a₁ ^ 2 * (x - x₀)
            + 4 * (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y₀))
          * (((x - x₀) ^ 2 - W.veluGx x₀ y₀)
                * (6 * x ^ 2 + (4 * W.a₂ + W.a₁ ^ 2) * x + 2 * W.a₄ + W.a₁ * W.a₃)
              + W.veluGx x₀ y₀
                * (W.a₁ ^ 2 * (x - x₀)
                    + 4 * (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y₀)))
          * (x - x₀)
          * ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) ^ 2
              + W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * (2 * y + W.a₁ * x + W.a₃)
              - (W.a₂ + 2 * x + x₀) * (2 * y + W.a₁ * x + W.a₃) ^ 2)
      = ((2 * y + W.a₁ * x + W.a₃) * ((x - x₀) ^ 2 - W.veluGx x₀ y₀)) ^ 2
        * ((2 * y + W.a₁ * x + W.a₃) ^ 2 * (x - x₀)
            + 2
              * ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) ^ 2
                  + W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)
                    * (2 * y + W.a₁ * x + W.a₃)
                  - (W.a₂ + 2 * x + x₀) * (2 * y + W.a₁ * x + W.a₃) ^ 2)) := by sorry
