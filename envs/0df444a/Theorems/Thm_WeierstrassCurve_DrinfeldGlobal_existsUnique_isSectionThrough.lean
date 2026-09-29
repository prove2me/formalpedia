-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_existsUnique_isSectionThrough
-- name    : WeierstrassCurve.DrinfeldGlobal.existsUnique_isSectionThrough
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/4a383b98-e8bf-555a-af63-c9dc76dc2022
-- title:
--   Unique section through an affine point of the projective model
-- statement:
--   Let $T$ be a commutative ring and let $W$ be a projective Weierstrass cubic over $T$, with associated graded ring $\mathrm{projModelGradingCR}\,W$ and projective model $\mathrm{Proj}(\mathrm{projModelGradingCR}\,W)$ over $\mathrm{Spec}\,T$ via the structure morphism `projModelStrCR W`. Let $x,y \in T$ satisfy the affine Weierstrass equation attached to $W$, i.e. `W.toAffine.Equation x y` ($y^2 + a_1xy + a_3y = x^3 + a_2x^2 + a_4x + a_6$). Then there is exactly one element $S$ of `Section W` — that is, one morphism $\mathrm{Spec}\,T \to \mathrm{Proj}(\mathrm{projModelGradingCR}\,W)$ whose composite with `projModelStrCR W` is the identity of $\mathrm{Spec}\,T$ — satisfying `IsSectionThrough S x y`, i.e. for which there exists a ring homomorphism $\chi$ from the degree-zero part `ZChartRing W` of the homogeneous localisation of $\mathrm{projModelGradingCR}\,W$ at the third coordinate `coord W 2` to $T$ such that the underlying morphism of $S$ equals $\mathrm{Spec}(\chi)$ followed by the chart inclusion `zChartι W`, and such that $\chi(\mathrm{xOverZ}\,W) = x$ and $\chi(\mathrm{yOverZ}\,W) = y$.
--
--   This is the scheme-theoretic form of the statement that the affine points of a Weierstrass cubic over a ring $T$ are exactly the $T$-sections of its projective model lying in the chart where the third coordinate is invertible, with the affine coordinates read off as the images of $X/Z$ and $Y/Z$. It is used to produce sections with prescribed coordinates, in particular in the construction of levels of the Drinfeld-type structures over dual numbers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_existsUnique_isSectionThrough.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.existsUnique_isSectionThrough
    {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T) (x y : T)
    (hxy : W.toAffine.Equation x y) :
    ∃! S : Section W, IsSectionThrough S x y := by sorry
