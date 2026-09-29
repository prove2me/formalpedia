-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_algHom_ext_of_forall_restrictAlong_placeOfPoint_eq
-- name    : WeierstrassCurve.Affine.algHom_ext_of_forall_restrictAlong_placeOfPoint_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/00c8479e-a9de-523d-aa65-d8e112a1ca60
-- title:
--   Integral maps into K(E) determined by action on places
-- statement:
--   Let $K$ be an algebraically closed field of characteristic zero and let $V$ be an affine Weierstrass curve over $K$ which is elliptic. Assume $V$ carries a genus-one place gate: a bijection `placeOfPoint` between the point group $V.\mathrm{Point}$ and the set of places of $V.\mathrm{FunctionField}$ over $K$ (a place being a valuation subring, distinct from the whole field, containing the image of $K$ and having principal ideals), all of whose places have degree $1$; assume the gate is centred, i.e. for every nonsingular affine point $(x,y)$ the classes of $X-x$ and $Y-y$ in the coordinate ring map into the nonunits of the valuation subring attached to $(x,y)$; and assume the Abel theorem holds for $V$, i.e. a divisor of degree $0$ is principal precisely when its image under `divisorSum` is $0$. Let $F'$ be a field with a $K$-algebra structure such that every place $w$ of $F'$ over $K$ is rational, meaning $K \to \kappa(w)$ is surjective onto the residue field. Let $\varphi_1,\varphi_2 : F' \to V.\mathrm{FunctionField}$ be $K$-algebra homomorphisms whose underlying ring homomorphisms are integral. If for every point $P$ of $V$ the pull-backs along $\varphi_1$ and along $\varphi_2$ of the place `placeOfPoint P` agree as places of $F'$ — that is, the two preimage valuation subrings coincide — then $\varphi_1 = \varphi_2$.
--
--   This is a rigidity statement: an integral $K$-embedding of a field into the function field of an elliptic curve is determined by the induced map on places, the pull-back of the place at each point of the curve. It is used in the construction of point homomorphisms from isogeny data, where equality of actions on places must be upgraded to equality of the corresponding pull-back maps on function fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_algHom_ext_of_forall_restrictAlong_placeOfPoint_eq.lean

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u

theorem WeierstrassCurve.Affine.algHom_ext_of_forall_restrictAlong_placeOfPoint_eq
    {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
    {V : WeierstrassCurve.Affine K} [V.IsElliptic]
    [GenusOnePlaceGate V] [GenusOnePlaceGate.IsCentred V] [AbelTheorem V]
    {F' : Type*} [Field F'] [Algebra K F'] (hrat : ∀ w : AlgebraicCurve.Place K F', w.IsRational)
    (φ₁ φ₂ : F' →ₐ[K] V.FunctionField)
    (hφ₁ : φ₁.toRingHom.IsIntegral) (hφ₂ : φ₂.toRingHom.IsIntegral)
    (hres : ∀ P : V.Point,
      (placeOfPoint P).restrictAlong φ₁ hφ₁ = (placeOfPoint P).restrictAlong φ₂ hφ₂) :
    φ₁ = φ₂ := by sorry
