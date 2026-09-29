-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_GroupLaws_mul_comm_schemeHomOver_of_isOriginIdentity
-- name    : WeierstrassCurve.DrinfeldGlobal.GroupLaws.mul_comm_schemeHomOver_of_isOriginIdentity
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/07e77dbf-55bc-5ea9-a43c-99c5560a734c
-- title:
--   Commutativity of the group law on arbitrary S-points
-- statement:
--   Let $A$ be a commutative ring and let $\mathcal G$ be a family of group laws over $A$, that is, an assignment to every commutative $A$-algebra $T$ and every projective Weierstrass curve $W$ over $T$ whose discriminant is a unit of a `RelativeGroupLaw` on the structure morphism $\mathrm{Proj}$ of the graded quotient ring of $W$ over $\mathrm{Spec}\,T$ (a functorial multiplication, unit and inverse on $T$-scheme points, satisfying associativity, the unit laws, left inverses and compatibility with base change of the test scheme). Assume $\mathcal G$ is chord–tangent, i.e. for every such $T$, $W$ and unit discriminant there is a bijection between the points over a field $F$ and the affine points of $W\otimes_T F$ which is additive for the law and equivariant for $A$-automorphisms of $F$; and assume $\mathcal G$ has the origin as identity, i.e. for every such $T$, $W$ there is a ring homomorphism $\chi$ from the origin chart ring of $W$ to $T$ cutting out the unit section of $\mathcal G$ over $\mathrm{Spec}\,T$ and killing both chart coordinates $xOverY$ and $zOverY$. Then for every commutative $A$-algebra $T$, every projective Weierstrass curve $W$ over $T$ with $\Delta(W)$ a unit, every scheme $S$ and morphism $t : S \to \mathrm{Spec}\,T$, and any two $S$-points $x,y$ over $t$ (morphisms to the projective model composing with the structure morphism to give $t$), one has $\mathrm{mul}\,t\,x\,y = \mathrm{mul}\,t\,y\,x$.
--
--   This is the commutativity of the chord–tangent group law on the projective model of an elliptic Weierstrass curve, stated for points valued in an arbitrary test scheme rather than only for global sections. It is used in the construction of isomorphisms of projective models compatible with Frobenius and with torsion sections in the Drinfeld-level part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_GroupLaws_mul_comm_schemeHomOver_of_isOriginIdentity.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.GroupLaws.mul_comm_schemeHomOver_of_isOriginIdentity
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ)
    {S : Scheme} (t : S ⟶ Spec (CommRingCat.of T)) (x y : SchemeHomOver t (projModelStrCR W)) :
    (𝒢 T W hΔ).mul t x y = (𝒢 T W hΔ).mul t y x := by sorry
