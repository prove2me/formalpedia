-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_exists_algEquiv_restrictAlong_placeOfPoint_eq_add
-- name    : WeierstrassCurve.Affine.exists_algEquiv_restrictAlong_placeOfPoint_eq_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/097a6011-2a0d-5fc7-ac08-6af7721d7d7f
-- title:
--   Translation by R as a function-field automorphism on places
-- statement:
--   Let $F$ be an algebraically closed field of characteristic zero and let $W$ be an affine Weierstrass curve over $F$ which is elliptic. Assume $W$ carries the data and properties packaged by three project classes: `GenusOnePlaceGate W`, consisting of a bijection `pointEquivPlace` between the group $W.\mathrm{Point}$ and the places of $W.\mathrm{FunctionField}$ over $F$ (a place being a valuation subring, not the whole field, containing the image of $F$ and a principal ideal ring) together with the assertion that every such place has degree $1$, where `placeOfPoint` denotes this bijection; `GenusOnePlaceGate.IsCentred W`, which says that for every nonsingular affine point $(x,y)$ the images in the function field of the coordinate-ring classes `CoordinateRing.XClass W x` and `CoordinateRing.YClass W (C y)` lie in the nonunits of the valuation subring of `placeOfPoint (Point.some x y h)`; and `AbelTheorem W`, which says that a divisor of degree $0$ is principal exactly when its image under `divisorSum` — the sum in $W.\mathrm{Point}$ of the points corresponding to its places, with multiplicities — is $0$. Then for every point $R$ of $W$ there exist an $F$-algebra automorphism $\tau$ of $W.\mathrm{FunctionField}$ and a proof that the underlying ring homomorphism of $\tau$ is integral, such that for every point $Q$ the restriction of `placeOfPoint Q` along $\tau$ — the place whose valuation subring is the preimage under $\tau$ of that of `placeOfPoint Q` — equals `placeOfPoint (Q + R)`.
--
--   This is the function-field form of translation by a point on an elliptic curve: the automorphism $\tau$ is the pull-back along $P \mapsto P + R$, and the conclusion records that it moves the place attached to $Q$ to the place attached to $Q+R$. It is used in the construction of homomorphisms of points from isogeny data, via [`WeierstrassCurve.Affine.IsogenyHomDatum.exists_pointHom_comp_eq_of_ker_le_of_isCentred`](thm.html#WeierstrassCurve.Affine.IsogenyHomDatum.exists_pointHom_comp_eq_of_ker_le_of_isCentred).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_exists_algEquiv_restrictAlong_placeOfPoint_eq_add.lean

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u

theorem WeierstrassCurve.Affine.exists_algEquiv_restrictAlong_placeOfPoint_eq_add
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    {W : WeierstrassCurve.Affine F} [W.IsElliptic]
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [AbelTheorem W]
    (R : W.Point) :
    ∃ (τ : W.FunctionField ≃ₐ[F] W.FunctionField) (hτ : τ.toAlgHom.toRingHom.IsIntegral),
      ∀ Q : W.Point, (placeOfPoint Q).restrictAlong τ.toAlgHom hτ = placeOfPoint (Q + R) := by sorry
