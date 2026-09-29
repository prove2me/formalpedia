-- Prove2me | Theorems.Thm_WeierstrassCurve_velu2_secant_negAddY_cleared_identity
-- name    : WeierstrassCurve.velu2_secant_negAddY_cleared_identity
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/0634fdec-f4e3-5bfc-817e-10aac3b00cf3
-- title:
--   Cleared secant identity for the order-2 Vélu map (ordinate)
-- statement:
--   Let $F$ be a field and $W$ a Weierstrass curve over $F$ with coefficients $a_1,a_2,a_3,a_4,a_6$, and let $x_0,y_0,x_1,y_1,x_2,y_2 \in F$ be such that $(x_1,y_1)$, $(x_2,y_2)$ and $(x_0,y_0)$ all satisfy the affine Weierstrass equation of $W$, that $2y_0 + a_1 x_0 + a_3 = 0$ (so $(x_0,y_0)$ is fixed by the involution $y \mapsto -y - a_1x - a_3$), and that $x_1 \neq x_2$. Write $\lambda =$ `W.toAffine.slope x₁ x₂ y₁ y₂` for the slope of the line through $(x_1,y_1)$ and $(x_2,y_2)$, $x_A =$ `W.toAffine.addX x₁ x₂ λ` for the abscissa of the third intersection point of that line with the curve, $\tilde y_A =$ `W.toAffine.negAddY x₁ x₂ y₁ λ` for its ordinate, and put $t =$ `W.veluGx x₀ y₀` $= 3x_0^2 + 2a_2x_0 + a_4 - a_1y_0$. Then
--   $$(x_2-x_0)(x_A-x_0)(x_2-x_A)(y_1-y_0) - (x_1-x_0)\bigl[(a_1(x_2-x_0)+y_2-y_0)(x_A-x_0)^2 - (a_1(x_A-x_0)+\tilde y_A-y_0)(x_2-x_0)^2\bigr] + t\bigl[(x_A-x_0)(y_2-y_0) - (x_2-x_0)(\tilde y_A-y_0)\bigr] = 0.$$
--
--   This is the denominator-cleared form of the assertion that Vélu's quotient map attached to the $2$-torsion point $(x_0,y_0)$, namely $(x,y) \mapsto \bigl(x + t/(x-x_0),\, y - t(a_1(x-x_0)+y-y_0)/(x-x_0)^2\bigr)$, carries a collinear triple on $W$ to a collinear triple on the quotient curve, in the secant case $x_1 \neq x_2$ and for the ordinate coordinate. It is used in the construction of the additive map underlying the order-$2$ Vélu point map, [`WeierstrassCurve.exists_addMonoidHom_coe_eq_veluPointMap2`](thm.html#WeierstrassCurve.exists_addMonoidHom_coe_eq_veluPointMap2).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_velu2_secant_negAddY_cleared_identity.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_Velu

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.velu2_secant_negAddY_cleared_identity
    {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {x₀ y₀ x₁ y₁ x₂ y₂ : F}
    (hP₁ : W.toAffine.Equation x₁ y₁)
    (hP₂ : W.toAffine.Equation x₂ y₂) (hQ : W.toAffine.Equation x₀ y₀)
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) (hx12 : x₁ ≠ x₂) :
    (x₂ - x₀)
          * (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₀)
          * (x₂ - W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))
          * (y₁ - y₀)
        - (x₁ - x₀)
          * ((W.a₁ * (x₂ - x₀) + y₂ - y₀)
                * (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₀) ^ 2
              - (W.a₁ * (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₀)
                    + W.toAffine.negAddY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂) - y₀)
                * (x₂ - x₀) ^ 2)
        + W.veluGx x₀ y₀
          * ((W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₀) * (y₂ - y₀)
              - (x₂ - x₀)
                * (W.toAffine.negAddY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂) - y₀))
      = 0 := by sorry
