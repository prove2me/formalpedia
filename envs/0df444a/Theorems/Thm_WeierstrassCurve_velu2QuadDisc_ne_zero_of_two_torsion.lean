-- Prove2me | Theorems.Thm_WeierstrassCurve_velu2QuadDisc_ne_zero_of_two_torsion
-- name    : WeierstrassCurve.velu2QuadDisc_ne_zero_of_two_torsion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/a457550b-ed8e-520f-a3c9-91fa02b786bc
-- title:
--   Nonvanishing of `velu2QuadDisc` at a 2-torsion point
-- statement:
--   Let $R$ be a commutative ring and let $W$ be a Weierstrass curve over $R$, with the usual associated quantities $a_1,a_3$, $b_2$, $b_4$ and discriminant $\Delta$ in Mathlib's sense. Let $x_0,y_0 \in R$ and assume: (i) $\Delta \neq 0$; (ii) the pair $(x_0,y_0)$ satisfies the affine Weierstrass equation of $W$, i.e. `W.toAffine.Equation x₀ y₀` holds; (iii) `W.veluGy x₀ y₀` vanishes, that is $-(2y_0 + a_1 x_0 + a_3) = 0$, which is the condition that the point $(x_0,y_0)$ be fixed by inversion, so of order dividing $2$. The conclusion is that `W.velu2QuadDisc x₀` is nonzero, i.e.
--   $$b_2^2 - 8 b_2 x_0 - 48 x_0^2 - 32 b_4 \neq 0$$
--   in $R$. No invertibility or integral-domain hypothesis on $R$ is imposed beyond $\Delta \neq 0$; note that over a field this quantity is the discriminant of the quadratic cofactor cutting out the two remaining abscissae of $2$-torsion, so its nonvanishing says those abscissae are distinct.
--
--   The statement records that at an affine point of order dividing $2$ on a curve with nonzero discriminant, the quadratic cofactor of the $2$-division polynomial has nonzero discriminant. It is used in the construction of the quotient curve by a subgroup of order $2$ in the Vélu formulae, where it enters the verification that the quotient curve again has nonzero discriminant ([`WeierstrassCurve.veluQuotient2_Delta_ne_zero`](thm.html#WeierstrassCurve.veluQuotient2_Delta_ne_zero)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_velu2QuadDisc_ne_zero_of_two_torsion.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_VeluOrderTwo

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace WeierstrassCurve
variable {R : Type*} [CommRing R] {W : WeierstrassCurve R}
open Affine

theorem velu2QuadDisc_ne_zero_of_two_torsion {x₀ y₀ : R} (hΔ : W.Δ ≠ 0)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) :
    W.velu2QuadDisc x₀ ≠ 0 := by sorry
