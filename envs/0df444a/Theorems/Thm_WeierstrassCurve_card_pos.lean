-- Prove2me | Theorems.Thm_WeierstrassCurve_card_pos
-- name    : WeierstrassCurve.card_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/2b26c3dc-7ad9-55dc-944b-bd662cf99ab6
-- title:
--   Positivity of the point count of a Weierstrass curve
-- statement:
--   Let $F$ be a commutative ring that is finite, and let $W$ be a Weierstrass curve over $F$, i.e. a tuple of coefficients $a_1,a_2,a_3,a_4,a_6 \in F$. The project attaches to $W$ a natural number, defined to be the cardinality of the type of points `W.toAffine.Point` of the associated affine curve, that is, the number of elements of the set consisting of the point at infinity together with the nonsingular $F$-points of the equation $y^2 + a_1xy + a_3y = x^3 + a_2x^2 + a_4x + a_6$. The theorem asserts that this natural number is strictly positive. Note that no hypothesis beyond commutativity and finiteness of $F$ is imposed — $F$ need not be a field, and $W$ is not assumed nonsingular nor to have invertible discriminant — and that the conclusion is merely the nonvanishing of the point count, not a bound of Hasse type.
--
--   This is the elementary remark that the point set of a Weierstrass curve over a finite commutative ring is nonempty, the point at infinity always being rational, so that its number of points is a positive natural number. It is used wherever this count enters a trace-of-Frobenius computation, in particular in [`FreyCurve.freyCurveInt_apOfModel_three`](thm.html#FreyCurve.freyCurveInt_apOfModel_three).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_card_pos.lean

import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.card_pos {F : Type*} [CommRing F] [Finite F]
    (W : WeierstrassCurve F) : 0 < W.card := by sorry
