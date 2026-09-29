-- Prove2me | Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_isOriginChartSection_iff_one_eq_kwZeroSect
-- name    : WeierstrassProjModel.RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/c64b48b9-9831-5dcd-8fbe-0c18f1b1fcf8
-- title:
--   Unit section factors through the origin chart iff it is [0:1:0]
-- statement:
--   Let $T$ be a commutative ring, $V$ a Weierstrass curve over $T$, and $G$ a relative group law on the structure morphism `projModelStrCR V.toProjective` from the $\operatorname{Proj}$ of the graded quotient ring attached to the projective Weierstrass model of $V$ to $\operatorname{Spec} T$; thus $G$ assigns functorially to each $T$-scheme a group structure on the set of sections, and $G.one (\mathbb{1})$ is the unit element for the identity morphism of $\operatorname{Spec} T$, i.e. a morphism $\operatorname{Spec} T \to \operatorname{Proj}$ together with a proof that it is a section of `projModelStrCR V.toProjective`. The theorem asserts the equivalence of two conditions. First: there exists a ring homomorphism $\chi$ from `OriginChartRing V.toProjective`, the degree-zero homogeneous localisation of the model ring away from the class `coord V.toProjective 1` of the variable $Y$, to $T$, such that `IsOriginChartSection` holds for the unit section and $\chi$ — that is, the underlying morphism of $G.one (\mathbb{1})$ equals $\operatorname{Spec}\chi$ followed by the chart morphism `originChartι V.toProjective` — and moreover $\chi$ annihilates both `xOverY V.toProjective` (the class of $X/Y$) and `zOverY V.toProjective` (the class of $Z/Y$). Second: the underlying morphism of $G.one (\mathbb{1})$ coincides with the underlying morphism of `kwZeroSect T V`, the section given by $\operatorname{Spec}$ of the evaluation map `kwYChartEval` followed by the canonical morphism `Proj.awayι` at the class of $Y$.
--
--   This is the dictionary between the two ways of saying that the identity of a relative group law on the projective Weierstrass model is the point at infinity: a chart-theoretic factorisation through $D_+(Y)$ with vanishing coordinates $X/Y$ and $Z/Y$, and equality with the explicit zero section $[0:1:0]$ of the group-law vocabulary. It is used wherever a hypothesis phrased in one of the two forms has to be fed into a construction demanding the other, and is invoked in the modular-curve developments downstream.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_RelativeGroupLaw_exists_isOriginChartSection_iff_one_eq_kwZeroSect.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal NeronModelInfra

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassProjModel.RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect
    {T : Type u} [CommRing T] (V : WeierstrassCurve T) (G : RelativeGroupLaw T (projModelStrCR V.toProjective)) :
    (∃ χ : OriginChartRing V.toProjective →+* T,
        IsOriginChartSection (G.one (𝟙 _)) χ ∧ χ (xOverY V.toProjective) = 0 ∧ χ (zOverY V.toProjective) = 0) ↔
      (G.one (𝟙 _)).1 = (kwZeroSect T V).1 := by sorry
