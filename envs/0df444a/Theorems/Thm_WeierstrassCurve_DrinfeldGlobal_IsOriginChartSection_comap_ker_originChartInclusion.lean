-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_IsOriginChartSection_comap_ker_originChartInclusion
-- name    : WeierstrassCurve.DrinfeldGlobal.IsOriginChartSection.comap_ker_originChartInclusion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/6a7aa52a-de16-54f3-8e76-611929420f84
-- title:
--   Section ideal restricted to the origin chart is kerχ
-- statement:
--   Let $T$ be a commutative ring and $W$ a Weierstrass curve over $T$. Write $\mathrm{Proj}(\text{projModelGradingCR})$ for the projective Weierstrass model of $W$, the $\mathrm{Proj}$ of the quotient grading of the homogeneous polynomial ring in three variables by the homogeneous ideal of $W$, with structure morphism `projModelStrCR` to $\operatorname{Spec} T$. Let $P$ be a section, i.e. a morphism $P.1$ from $\operatorname{Spec} T$ to this $\mathrm{Proj}$ whose composite with `projModelStrCR` is the identity of $\operatorname{Spec} T$. Let $\chi$ be a ring homomorphism from `OriginChartRing W`, the degree-zero homogeneous localisation of the model's graded ring away from the class of the second coordinate variable, to $T$, and assume `IsOriginChartSection P χ`, that is, $P.1$ equals $\operatorname{Spec}(\chi)$ followed by the origin-chart inclusion `originChartι W` of that localisation's spectrum into the $\mathrm{Proj}$. The conclusion is an equality of ideal sheaf data on $\operatorname{Spec}(\text{OriginChartRing } W)$: the pullback (`comap`) along `originChartι W` of the kernel ideal sheaf of $P.1$ coincides with the kernel ideal sheaf of $\operatorname{Spec}(\chi)$, i.e. with the ideal cut out by $\ker\chi$.
--
--   This identifies, on the origin chart of the projective Weierstrass model, the ideal of the closed subscheme defined by a section with the kernel of the affine coordinate map $\chi$ describing that section; it is the chart-level translation needed to read divisor-theoretic statements at the origin in terms of the local ring of the chart. It is used by [`WeierstrassCurve.DrinfeldGlobal.IsOriginChartSection.map_ideal_comap_ker_eq_ker`](thm.html#WeierstrassCurve.DrinfeldGlobal.IsOriginChartSection.map_ideal_comap_ker_eq_ker).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_IsOriginChartSection_comap_ker_originChartInclusion.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_FormalGroup_NSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing
  HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.IsOriginChartSection.comap_ker_originChartInclusion
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) (P : Section W) (χ : OriginChartRing W →+* T)
    (hP : IsOriginChartSection P χ) :
    (Scheme.Hom.ker P.1).comap (originChartι W) = Scheme.Hom.ker (Spec.map (CommRingCat.ofHom χ)) := by sorry
