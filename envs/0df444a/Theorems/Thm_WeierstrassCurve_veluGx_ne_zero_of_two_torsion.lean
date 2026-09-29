-- Prove2me | Theorems.Thm_WeierstrassCurve_veluGx_ne_zero_of_two_torsion
-- name    : WeierstrassCurve.veluGx_ne_zero_of_two_torsion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/ebb95932-53b0-5854-ab26-07734a6bf632
-- title:
--   Nonvanishing of gₓ at a 2-torsion point
-- statement:
--   Let $R$ be a commutative ring and let $W$ be a Weierstrass curve over $R$ with coefficients $a_1, a_2, a_3, a_4, a_6$, and let $x_0, y_0 \in R$. Assume three things: the discriminant $\Delta$ of $W$ is not zero in $R$; the pair $(x_0, y_0)$ satisfies the affine Weierstrass equation of $W$, i.e. $y_0^2 + a_1 x_0 y_0 + a_3 y_0 = x_0^3 + a_2 x_0^2 + a_4 x_0 + a_6$; and the quantity `veluGy` of $W$ at $(x_0,y_0)$, namely $-(2y_0 + a_1 x_0 + a_3)$, vanishes, which expresses that the point $(x_0,y_0)$ is fixed by the Weierstrass involution, i.e. is $2$-torsion. The conclusion is that the quantity `veluGx` of $W$ at $(x_0,y_0)$, namely
--   $$3x_0^2 + 2a_2 x_0 + a_4 - a_1 y_0,$$
--   is not zero in $R$.
--
--   This is the statement that the abscissa of a $2$-torsion point on a curve of invertible (in particular nonzero) discriminant is a simple root of the $2$-division polynomial, in the form of the nonvanishing of the partial derivative in $x$ of the Weierstrass equation. It supplies the nondegeneracy input for the construction of the Vélu quotient by a subgroup of order $2$, and is used in establishing the nonvanishing of the discriminant of that quotient and the surjectivity and function-field properties of the associated degree-$2$ map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_veluGx_ne_zero_of_two_torsion.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_VeluOrderTwo

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace WeierstrassCurve
variable {R : Type*} [CommRing R] {W : WeierstrassCurve R}
open Affine

theorem veluGx_ne_zero_of_two_torsion {x₀ y₀ : R} (hΔ : W.Δ ≠ 0)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) :
    W.veluGx x₀ y₀ ≠ 0 := by sorry
