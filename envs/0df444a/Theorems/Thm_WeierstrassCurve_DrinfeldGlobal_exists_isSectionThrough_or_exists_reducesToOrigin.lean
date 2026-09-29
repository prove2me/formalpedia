-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_isSectionThrough_or_exists_reducesToOrigin
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_isSectionThrough_or_exists_reducesToOrigin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/29dfd80e-37aa-5a47-82b9-068b96e88c59
-- title:
--   Local dichotomy for sections of a projective Weierstrass model
-- statement:
--   Let $T$ be a commutative local ring, let $W$ be a projective Weierstrass cubic over $T$, and let $S$ be a section of the projective model of $W$, that is, a morphism $S.1 : \operatorname{Spec} T \to \operatorname{Proj}$ of the graded quotient ring `projModelGradingCR W` whose composite with the structure morphism `projModelStrCR W` is the identity of $\operatorname{Spec} T$. Then at least one of the following holds. Either there are elements $x, y \in T$ with `IsSectionThrough S x y`, i.e. a ring homomorphism $\chi$ from `ZChartRing W`, the degree-zero homogeneous localisation of the model away from the coordinate $Z =$ `coord W 2`, to $T$ such that $S.1$ equals $\operatorname{Spec}(\chi)$ followed by the chart immersion `zChartι W`, and $\chi(xOverZ\ W) = x$, $\chi(yOverZ\ W) = y$. Or there is a ring homomorphism $\chi$ from `OriginChartRing W`, the homogeneous localisation away from $Y =$ `coord W 1`, to $T$ with `ReducesToOrigin S χ (maximalIdeal T)`: $S.1$ equals $\operatorname{Spec}(\chi)$ followed by `originChartι W`, and both $-\chi(xOverY\ W)$ and $-\chi(zOverY\ W)$ lie in the maximal ideal of $T$. The two alternatives are not asserted to be exclusive.
--
--   This is the standard dichotomy for a point of a Weierstrass model over a local ring: the section either lies in the affine chart $Z \neq 0$, with well-defined affine coordinates $x = X/Z$, $y = Y/Z$, or it specialises at the closed point to the origin $[0:1:0]$ and so lives in the chart $Y \neq 0$ with $X/Y$ and $Z/Y$ non-units. It is used when sections of the projective model are compared with formal or Tate-parameter data, for instance in the analysis of Tate points on modular curves and in the statement that such lifts form a line.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_isSectionThrough_or_exists_reducesToOrigin.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_isSectionThrough_or_exists_reducesToOrigin
    {T : Type u} [CommRing T] [IsLocalRing T] (W : WeierstrassCurve.Projective T) (S : Section W) :
    (∃ x y : T, IsSectionThrough S x y) ∨ (∃ χ : OriginChartRing W →+* T, ReducesToOrigin S χ (maximalIdeal T)) := by sorry
