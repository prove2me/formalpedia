-- Prove2me | Theorems.Thm_WeierstrassCurve_ofPowerSeries_invDiff_mul_eq_derivative_laurentFrame
-- name    : WeierstrassCurve.ofPowerSeries_invDiff_mul_eq_derivative_laurentFrame
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/e515e146-53da-5ba8-816d-6ec6fb23488a
-- title:
--   Formal invariant differential equals dx/(2y+a₁x+a₃) in the Laurent frame
-- statement:
--   Let $R$ be a commutative ring, let $W$ be a Weierstrass curve over $R$ with coefficients $a_1,a_2,a_3,a_4,a_6$, and let $G$ be a formal group over $R$ whose underlying two-variable power series `G.toPowerSeries` is the formal group law `W.formalGroupLawFixed` attached to $W$ (the substitution of the series `W.fgZ3Fixed` into the inversion series `W.fgInv`). Write $\omega :=$ `G.invDiff` $=$ `PowerSeries.invOfUnit` of `G.invDiffDenom` at the unit $1$, where `G.invDiffDenom` is obtained from the partial derivative of $G$ in its first variable by substituting $(0,z)$, so that $\omega$ is the inverse of $\partial_1G(0,z)$; and let $u :=$ `W.wUnitFactor` $= 1-(a_1z+a_2z^2+a_3w+a_4zw+a_6w^2)$, with $w :=$ `W.formalW` the power series whose $n$-th coefficient is the $n$-th coefficient of `W.wIter n`. The assertion is an identity in the Laurent series $R((z)) =$ `LaurentSeries R`: setting $x := z^{-2}u$ and $y := -z^{-3}u$ (images of $u$ under `HahnSeries.ofPowerSeries` multiplied by the monomials `HahnSeries.single (-2) 1`, resp. `HahnSeries.single (-3) 1`), one has
--   $$\omega\cdot\bigl(2y+a_1x+a_3\bigr) \;=\; \frac{d}{dz}\,x,$$
--   the derivative being `LaurentSeries.derivative R` and $a_1,a_3$ entering as the constant Laurent series `HahnSeries.C`.
--
--   This is the formal-group form of the statement that the invariant differential of a Weierstrass curve is $dx/(2y+a_1x+a_3)$: in the parameter $z=-x/y$, with $x=z^{-2}u$, $y=-z^{-3}u$, the normalised invariant differential $\bigl(\partial_1F(0,z)\bigr)^{-1}$ of the formal group law of $W$ is exactly $dx/(2y+a_1x+a_3)$. It is used by [`WeierstrassCurve.exists_laurent_frame_invDiff_mul_eq_derivative`](thm.html#WeierstrassCurve.exists_laurent_frame_invDiff_mul_eq_derivative).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_ofPowerSeries_invDiff_mul_eq_derivative_laurentFrame.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup

theorem WeierstrassCurve.ofPowerSeries_invDiff_mul_eq_derivative_laurentFrame
    {R : Type*} [CommRing R] (W : WeierstrassCurve R) (G : FormalGroup R)
    (hG : G.toPowerSeries = W.formalGroupLawFixed) :
    HahnSeries.ofPowerSeries ℤ R G.invDiff *
        (2 * (-(HahnSeries.single (-3 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R W.wUnitFactor)) + HahnSeries.C W.a₁ * (HahnSeries.single (-2 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R W.wUnitFactor) + HahnSeries.C W.a₃)
      = LaurentSeries.derivative R (HahnSeries.single (-2 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R W.wUnitFactor) := by sorry
