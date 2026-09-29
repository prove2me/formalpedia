-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_exists_algEquiv_forall_restrictAlong_placeOfPoint_eq_add
-- name    : WeierstrassCurve.Affine.exists_algEquiv_forall_restrictAlong_placeOfPoint_eq_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/9506b8fa-519c-5056-987e-4bf32c70eb6b
-- title:
--   Translation by a point as a function-field automorphism
-- statement:
--   Let $F$ be an algebraically closed field and let $W$ be an affine Weierstrass curve over $F$ which is elliptic. Assume $W$ carries a `GenusOnePlaceGate`, that is, a bijection `pointEquivPlace` between the group $W$.`Point` of $F$-points of $W$ (with the point at infinity as zero) and the set of places of $W$.`FunctionField` over $F$ — where a place is a proper valuation subring containing the image of $F$ and whose ring is a principal ideal ring — such that every such place has degree $1$; write `placeOfPoint` for this bijection. Assume moreover that the gate is centred: for every pair $(x,y)$ with `W.Nonsingular x y`, the images in the function field of the coordinate-ring classes `XClass W x` and `YClass W (C y)` are nonunits of the valuation subring of `placeOfPoint (Point.some x y h)`; and assume `AbelTheorem` for $W$: a divisor of degree $0$ is principal exactly when its `divisorSum` — the $\mathbb{Z}$-linear extension of $v \mapsto$ `pointEquivPlace.symm v` — vanishes. Then for every point $R$ of $W$ there exist an $F$-algebra automorphism $\tau$ of $W$.`FunctionField` and a proof that the underlying ring homomorphism of $\tau$ is integral, such that for every point $Q$ the restriction of `placeOfPoint Q` along $\tau$ — the place whose valuation subring is the preimage under $\tau$ of that of `placeOfPoint Q` — is `placeOfPoint (Q + R)`.
--
--   This is the function-field form of the statement that translation by $R$ is an automorphism of the elliptic curve carrying $Q$ to $Q+R$, the map $\tau_R$ of the classical theory, here recorded as a single automorphism of the function field compatible with the point–place dictionary for all $Q$ simultaneously. It is used in the construction of isogeny data, namely by [`WeierstrassCurve.Affine.IsogenyHomDatum.exists_pointHom_comp_eq_of_ker_le_of_separableAlong`](thm.html#WeierstrassCurve.Affine.IsogenyHomDatum.exists_pointHom_comp_eq_of_ker_le_of_separableAlong), to normalise a homomorphism of function fields by composing with translations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_exists_algEquiv_forall_restrictAlong_placeOfPoint_eq_add.lean

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u

theorem WeierstrassCurve.Affine.exists_algEquiv_forall_restrictAlong_placeOfPoint_eq_add
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F]
    {W : WeierstrassCurve.Affine F} [W.IsElliptic]
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [AbelTheorem W]
    (R : W.Point) :
    ∃ (τ : W.FunctionField ≃ₐ[F] W.FunctionField) (hτ : τ.toAlgHom.toRingHom.IsIntegral),
      ∀ Q : W.Point, (placeOfPoint Q).restrictAlong τ.toAlgHom hτ = placeOfPoint (Q + R) := by sorry
