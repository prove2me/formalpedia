-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq
-- name    : WeierstrassCurve.Affine.algHom_eq_of_forall_restrictAlong_placeOfPoint_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/a78512c0-1f5a-5373-bbf2-2dd29388d97f
-- title:
--   An integral K-embedding into K(E) is determined by its action on places
-- statement:
--   Let $K$ be an algebraically closed field and let $V$ be an affine Weierstrass curve over $K$ that is elliptic, equipped with: a `GenusOnePlaceGate` structure, i.e. a bijection `pointEquivPlace` between the group $V(K)$ of points of $V$ and the places of $K$ in the function field $V$.`FunctionField` (a place being a valuation subring containing the image of $K$, different from the whole field, whose ideals are principal) together with the statement that every such place has degree $1$; the centredness hypothesis `GenusOnePlaceGate.IsCentred`, that for every nonsingular pair $(x,y)$ the images in the function field of the coordinate-ring classes `XClass V x` and `YClass V (C y)` lie in the nonunits of the valuation subring of the place `placeOfPoint (Point.some x y h)`; and `AbelTheorem V`, that a divisor of degree $0$ is principal exactly when its image under `divisorSum` vanishes. Let $F'$ be a field with a $K$-algebra structure all of whose places $w$ over $K$ are rational, in the sense that $K \to$ `w.ResidueField` is surjective. Let $\varphi_1, \varphi_2 \colon F' \to V.$`FunctionField` be $K$-algebra homomorphisms whose underlying ring homomorphisms are integral, and suppose that for every point $P$ of $V$ the pullbacks along $\varphi_1$ and along $\varphi_2$ of the place `placeOfPoint P` agree, i.e. the two valuation subrings of $F'$ obtained by comap coincide. Then $\varphi_1 = \varphi_2$.
--
--   This is the faithfulness statement for the dictionary between integral $K$-embeddings of a field $F'$ into the function field of an elliptic curve and the induced maps on places: the embedding is recovered from its action on the places attached to the points of $V$. It is used in the construction of point homomorphisms from isogeny data, specifically by [`WeierstrassCurve.Affine.IsogenyHomDatum.exists_pointHom_comp_eq_of_ker_le_of_separableAlong`](thm.html#WeierstrassCurve.Affine.IsogenyHomDatum.exists_pointHom_comp_eq_of_ker_le_of_separableAlong).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.lean

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u

theorem WeierstrassCurve.Affine.algHom_eq_of_forall_restrictAlong_placeOfPoint_eq
    {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K]
    {V : WeierstrassCurve.Affine K} [V.IsElliptic]
    [GenusOnePlaceGate V] [GenusOnePlaceGate.IsCentred V] [AbelTheorem V]
    {F' : Type*} [Field F'] [Algebra K F'] (hrat : ∀ w : AlgebraicCurve.Place K F', w.IsRational)
    (φ₁ φ₂ : F' →ₐ[K] V.FunctionField)
    (hφ₁ : φ₁.toRingHom.IsIntegral) (hφ₂ : φ₂.toRingHom.IsIntegral)
    (hres : ∀ P : V.Point,
      (placeOfPoint P).restrictAlong φ₁ hφ₁ = (placeOfPoint P).restrictAlong φ₂ hφ₂) :
    φ₁ = φ₂ := by sorry
