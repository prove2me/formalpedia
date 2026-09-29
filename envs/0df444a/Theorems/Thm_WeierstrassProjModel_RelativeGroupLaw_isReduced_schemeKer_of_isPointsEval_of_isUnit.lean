-- Prove2me | Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_isReduced_schemeKer_of_isPointsEval_of_isUnit
-- name    : WeierstrassProjModel.RelativeGroupLaw.isReduced_schemeKer_of_isPointsEval_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/a1f0560e-ea8a-5896-b60b-3933cc784d5b
-- title:
--   Reducedness of the n-torsion scheme for invertible n
-- statement:
--   Let $B$ be a commutative ring which is a domain and let $V$ be a projective Weierstrass curve over $B$ whose associated affine curve is elliptic. Let $G$ be a relative group law on the structure morphism `projModelStrCR V` from the $\mathrm{Proj}$ of the graded quotient ring attached to $V$ to $\operatorname{Spec} B$, i.e. a functorial multiplication, unit and inverse on the sets of $T$-sections $\{\varphi : T \to \mathrm{Proj} \mid \varphi \text{ followed by the structure morphism} = t\}$, for arbitrary $t : T \to \operatorname{Spec} B$, satisfying associativity, the two unit laws, left inversion and compatibility with base change along morphisms $T' \to T$ over $\operatorname{Spec} B$. Let $ev$ be a family, indexed by fields $F$ equipped with a $B$-algebra structure, of bijections between the sections over $\operatorname{Spec}$ of $B \to F$ and the affine points of the base change $V_F$, and assume the predicate `IsPointsEval` for $V$, $G$ and $ev$: each $ev_F$ carries $G$'s multiplication to addition of points, and commutes with the twist by any $B$-algebra automorphism $\sigma$ of $F$ on one side and `Point.map` of $\sigma$ on the other. Let $n$ be a natural number with $0 < n$ whose image in $B$ is a unit. Then the scheme `G.schemeKer n`, the pullback of the $n$-fold multiplication morphism $[n]_G$ of the model along the unit section over $\operatorname{Spec} B$, is reduced.
--
--   This is the reducedness half of the classical statement that the $n$-torsion subscheme $E[n]$ of an elliptic curve is finite étale over the base when $n$ is invertible. It is used in the Drinfeld-level results identifying $n$-torsion sections with zeros of division polynomials, in particular for $n = 2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_RelativeGroupLaw_isReduced_schemeKer_of_isPointsEval_of_isUnit.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.RelativeGroupLaw.isReduced_schemeKer_of_isPointsEval_of_isUnit
    {B : Type} [CommRing B] [IsDomain B] (V : WeierstrassCurve.Projective B)
    [V.toAffine.IsElliptic] (G : RelativeGroupLaw B (projModelStrCR V))
    (ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra B F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap B F))) (projModelStrCR V) ≃
        (V.baseChange F).toAffine.Point)
    (hev : IsPointsEval V G ev) {n : ℕ} (hn : IsUnit ((n : ℕ) : B)) (hn0 : 0 < n) :
    IsReduced (G.schemeKer n) := by sorry
