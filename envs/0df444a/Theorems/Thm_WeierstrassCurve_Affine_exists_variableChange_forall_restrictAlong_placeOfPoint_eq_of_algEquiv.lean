-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_exists_variableChange_forall_restrictAlong_placeOfPoint_eq_of_algEquiv
-- name    : WeierstrassCurve.Affine.exists_variableChange_forall_restrictAlong_placeOfPoint_eq_of_algEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/58bf56b8-5983-5040-9b89-5865b7f43a5a
-- title:
--   Isomorphism of function fields matching 𝒪 is a variable change
-- statement:
--   Let $F$ be an algebraically closed field with decidable equality, and let $W_1$, $W_2$ be affine Weierstrass curves over $F$ that are elliptic. Each of $W_1$, $W_2$ is assumed to carry a `GenusOnePlaceGate` structure, that is, a bijection `placeOfPoint` from its group of points to the set of places of its function field over $F$ (a place being a valuation subring containing the image of $F$, different from the whole field, and a principal ideal ring) all of whose places have degree $1$; and these structures are assumed centred (`GenusOnePlaceGate.IsCentred`): for every $x,y \in F$ with $W$ nonsingular at $(x,y)$, the coordinate-ring classes of $X - x$ and of $Y - y$ lie in the nonunits of the valuation subring of the place attached to the point $(x,y)$. Let $e : F(W_2) \xrightarrow{\sim} F(W_1)$ be an $F$-algebra isomorphism whose underlying ring homomorphism is integral, and assume that the restriction of the place attached to $0 \in W_1(F)$ along $e$, i.e. the pullback of its valuation subring under $e$, is the place attached to $0 \in W_2(F)$. Then there exists a Weierstrass variable change $C$ over $F$ with $C \bullet W_2 = W_1$ such that for every point $P$ of $W_1$ the restriction of the place attached to $P$ along $e$ equals the place attached to the image of $P$ under the bijection $W_1(F) \simeq W_2(F)$ determined by the equality $C \bullet W_2 = W_1$.
--
--   This is the effective form of the classical statement that an isomorphism of the function fields of two Weierstrass models which preserves the point at infinity is induced by a substitution $x = u^2x' + r$, $y = u^3y' + u^2sx' + t$, sharpened by the assertion that the induced map on places is exactly the point bijection of that coordinate change. It is used in the construction of variable changes from isomorphisms of function-field quotients, in [`WeierstrassCurve.exists_variableChange_eq_fullKernelQuotient_fullKernelQuotient_comp_eq_smul`](thm.html#WeierstrassCurve.exists_variableChange_eq_fullKernelQuotient_fullKernelQuotient_comp_eq_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_exists_variableChange_forall_restrictAlong_placeOfPoint_eq_of_algEquiv.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine

universe u

theorem WeierstrassCurve.Affine.exists_variableChange_forall_restrictAlong_placeOfPoint_eq_of_algEquiv
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F]
    {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
    [GenusOnePlaceGate W₁] [GenusOnePlaceGate.IsCentred W₁]
    [GenusOnePlaceGate W₂] [GenusOnePlaceGate.IsCentred W₂]
    (e : W₂.FunctionField ≃ₐ[F] W₁.FunctionField) (he : e.toAlgHom.toRingHom.IsIntegral)
    (hinf : (placeOfPoint (0 : W₁.Point)).restrictAlong e.toAlgHom he = placeOfPoint (0 : W₂.Point)) :
    ∃ (C : WeierstrassCurve.VariableChange F) (hC : C • W₂ = W₁),
      ∀ P : W₁.Point, (placeOfPoint P).restrictAlong e.toAlgHom he
        = placeOfPoint (Point.equivOfVariableChangeEq hC P) := by sorry
