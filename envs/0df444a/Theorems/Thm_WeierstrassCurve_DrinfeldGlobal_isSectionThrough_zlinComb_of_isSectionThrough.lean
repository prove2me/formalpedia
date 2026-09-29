-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isSectionThrough_zlinComb_of_isSectionThrough
-- name    : WeierstrassCurve.DrinfeldGlobal.isSectionThrough_zlinComb_of_isSectionThrough
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/a151c780-d4a7-5557-9b3a-0e34ef399f5f
-- title:
--   Integer combinations of sections pass through the combined points
-- statement:
--   Let $A$ be a commutative ring and let $\mathcal{G}$ be a family of group laws over $A$, that is, an assignment to every commutative $A$-algebra $T$, every Weierstrass curve $W$ in projective form over $T$ and every proof that the discriminant $W.\Delta$ is a unit, of a relative group law on the projective model of $W$. Assume $\mathcal{G}$ is chord–tangent, i.e.\ for all such $T$, $W$, $h\Delta$ there is a points-evaluation `ev` satisfying `IsPointsEval W (𝒢 T W hΔ)`, and assume $\mathcal{G}$ has the origin as identity, i.e.\ for all such data there is a ring homomorphism $\chi$ from the origin chart ring of $W$ to $T$ which presents the unit section $(\mathcal{G}\,T\,W\,h\Delta).\mathrm{one}(\mathbf 1)$ as an origin-chart section and kills $x/y$ and $z/y$. Let $T$ be a field that is an $A$-algebra, $W$ a projective Weierstrass curve over $T$ with $W.\Delta$ a unit, and let $S,S'$ be sections of the projective model over $\operatorname{Spec} T$ (morphisms composing with the structure morphism to the identity). Let $x,y,x',y' \in T$ and suppose $S$ passes through $(x,y)$ and $S'$ through $(x',y')$, in the sense that each is of the form $\operatorname{Spec}$ of a ring homomorphism from the $z$-chart ring of $W$ to $T$ followed by the $z$-chart inclusion, with the affine coordinates of that homomorphism equal to $(x,y)$, respectively $(x',y')$. Let $a,b \in \mathbb{Z}$. Write $P = a \cdot \mathrm{toPoint}\,W\,x\,y + b \cdot \mathrm{toPoint}\,W\,x'\,y'$ in the group of affine points $W.\mathrm{toAffine}.\mathrm{Point}$, where $\mathrm{toPoint}\,W\,u\,v$ is the point $(u,v)$ when it is nonsingular and $0$ otherwise, and let $aS + bS' := \mathrm{zlinComb}$, the $\mathcal{G}$-product of the $a$-fold and $b$-fold $\mathbb{Z}$-multiples of $S$ and $S'$. Then: if $P = 0$ then $aS + bS'$ equals the unit section; and for all $x_r,y_r \in T$ with $(x_r,y_r)$ nonsingular on $W.\mathrm{toAffine}$, if $P$ is the point $(x_r,y_r)$ then $aS+bS'$ passes through $(x_r,y_r)$ in the above sense.
--
--   This is the dictionary between sections of the projective model over a field and points of the Mordell–Weil group: it says that forming integer linear combinations with the relative group law corresponds to forming them in $W(T)$, read off in affine coordinates on the $z$-chart. It is used in the level structure constructions for the Drinfeld moduli problem, for instance when relabelling level structures and identifying cusp data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_isSectionThrough_zlinComb_of_isSectionThrough.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal ModularCurve.LevelRelabelling
open scoped Classical

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.isSectionThrough_zlinComb_of_isSectionThrough
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    {T : Type} [Field T] [Algebra A T] (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ)
    (S S' : Section W) (x y x' y' : T)
    (hS : IsSectionThrough S x y) (hS' : IsSectionThrough S' x' y') (a b : ℤ) :
    (a • toPoint W x y + b • toPoint W x' y' = 0 →
        zlinComb (𝒢 T W hΔ) S S' a b = (𝒢 T W hΔ).one (𝟙 _)) ∧
    (∀ (xr yr : T) (hr : W.toAffine.Nonsingular xr yr),
        a • toPoint W x y + b • toPoint W x' y' = WeierstrassCurve.Affine.Point.some xr yr hr →
        IsSectionThrough (zlinComb (𝒢 T W hΔ) S S' a b) xr yr) := by sorry
