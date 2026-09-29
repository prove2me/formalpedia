-- Prove2me | Theorems.Thm_WeierstrassCurve_veluQuotient2_j
-- name    : WeierstrassCurve.veluQuotient2_j
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/1dae4db4-37ac-5eec-98e7-5ba71e141eac
-- title:
--   j-invariant of the order-two Vélu quotient
-- statement:
--   Let $F$ be a field and let $W$ be a Weierstrass curve over $F$ that is elliptic (its discriminant $\Delta$ is a unit), and let $x_0, y_0 \in F$. Assume that $(x_0,y_0)$ satisfies the affine Weierstrass equation of $W$, and that $W.\mathrm{veluGy}(x_0,y_0) = -(2y_0 + a_1 x_0 + a_3)$ vanishes, i.e. the point is its own negative. Write $g_x = W.\mathrm{veluGx}(x_0,y_0) = 3x_0^2 + 2a_2 x_0 + a_4 - a_1 y_0$ and $d = W.\mathrm{velu2QuadDisc}(x_0) = b_2^2 - 8 b_2 x_0 - 48 x_0^2 - 32 b_4$, and let $W' = W.\mathrm{veluQuotient2}(x_0,y_0)$ be the Weierstrass curve with $a_1' = a_1$, $a_2' = a_2$, $a_3' = a_3$, $a_4' = a_4 - 5 g_x$ and $a_6' = a_6 - b_2 g_x - 7 x_0 g_x$. Under these hypotheses $W'$ is again elliptic (the instance being supplied by `isElliptic_veluQuotient2_of_isElliptic`, so that the $j$-invariant of $W'$ is defined), and the conclusion is the closed formula
--   $$j(W') = \frac{(c_4 + 240\, g_x)^3}{g_x \cdot d^2},$$
--   with $c_4 = W.c_4$ the usual invariant of $W$.
--
--   This is the explicit form of the $j$-invariant of the quotient of an elliptic curve by a subgroup of order two, in Vélu's coordinates: both numerator and denominator are polynomials in the Weierstrass coefficients of $W$ and in $x_0, y_0$. It is used in the moduli layer, where the two roots of the fibre polynomial of the modular equation $\Phi_2$ are matched with the $j$-invariants of the two-isogeny quotients ([`ModularCurve.fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j`](thm.html#ModularCurve.fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j)), and in the rigidity statement [`WeierstrassCurve.eq_of_veluQuotient2_j_eq_of_not_isIntegral_j`](thm.html#WeierstrassCurve.eq_of_veluQuotient2_j_eq_of_not_isIntegral_j).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_veluQuotient2_j.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import Theorems.Thm_WeierstrassCurve_isElliptic_veluQuotient2_of_isElliptic
import Theorems.Thm_WeierstrassCurve_veluQuotient2_Delta_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace WeierstrassCurve
variable {F : Type*} [Field F] {W : WeierstrassCurve F} [W.IsElliptic] {x₀ y₀ : F}
open Affine

theorem veluQuotient2_j (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) :
    haveI : (W.veluQuotient2 x₀ y₀).IsElliptic :=
      isElliptic_veluQuotient2_of_isElliptic hQ hgy
    (W.veluQuotient2 x₀ y₀).j
      = (W.c₄ + 240 * W.veluGx x₀ y₀) ^ 3
        / (W.veluGx x₀ y₀ * W.velu2QuadDisc x₀ ^ 2) := by sorry
