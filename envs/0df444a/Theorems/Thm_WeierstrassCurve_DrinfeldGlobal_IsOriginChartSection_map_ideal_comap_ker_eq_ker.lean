-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_IsOriginChartSection_map_ideal_comap_ker_eq_ker
-- name    : WeierstrassCurve.DrinfeldGlobal.IsOriginChartSection.map_ideal_comap_ker_eq_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/2516cc8a-a3de-5a9b-9659-c14c6a9416cc
-- title:
--   Origin-chart section: restricted graph ideal equals kerχ
-- statement:
--   Let $T$ be a commutative ring and $W$ a Weierstrass curve over $T$, with $\operatorname{Proj}$ of the graded quotient ring `projModelGradingCR W` as its projective model and structure morphism `projModelStrCR W` to $\operatorname{Spec} T$. Let $P$ be a section, that is a pair consisting of a morphism $P.1 : \operatorname{Spec} T \to \operatorname{Proj}$ together with the identity $P.1$ followed by `projModelStrCR W` $=\mathrm{id}_{\operatorname{Spec} T}$, and let $\chi$ be a ring homomorphism from the origin chart ring $\mathrm{OriginChartRing}\,W$ — the degree-zero homogeneous localisation of the homogeneous coordinate ring of the model away from the coordinate `coord W 1`, the class of $X_1$ — to $T$. Assume `IsOriginChartSection P χ`, i.e. $P.1$ equals $\operatorname{Spec}$ of $\chi$ followed by the open immersion `originChartι W` of that chart. Then the following two ideals of $\mathrm{OriginChartRing}\,W$ agree: the value on the affine open $\top$ of the pullback along `originChartι W` of the kernel ideal sheaf `Scheme.Hom.ker P.1`, transported along the isomorphism $\Gamma(\operatorname{Spec} R)\cong R$ of `Scheme.ΓSpecIso`, and the kernel of $\chi$.
--
--   This identifies, at the level of ideals of the chart ring, the graph ideal of a section passing through the origin chart with the kernel of the associated chart homomorphism. It is used downstream in the analysis of divisors supported at the origin, for instance in computing the product of graph ideals of a Drinfeld basis and in the comparison of the $n$-series with a product of linear factors in the origin parameter.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_IsOriginChartSection_map_ideal_comap_ker_eq_ker.lean

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

theorem WeierstrassCurve.DrinfeldGlobal.IsOriginChartSection.map_ideal_comap_ker_eq_ker
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) (P : Section W) (χ : OriginChartRing W →+* T)
    (hP : IsOriginChartSection P χ) :
    Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (OriginChartRing W))).hom.hom
      (((Scheme.Hom.ker P.1).comap (originChartι W)).ideal ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩) =
      RingHom.ker χ := by sorry
