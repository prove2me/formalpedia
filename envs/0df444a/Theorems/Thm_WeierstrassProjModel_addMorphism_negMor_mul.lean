-- Prove2me | Theorems.Thm_WeierstrassProjModel_addMorphism_negMor_mul
-- name    : WeierstrassProjModel.addMorphism_negMor_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/40159c54-9f89-50f8-8c04-f400f752e109
-- title:
--   Inverse law for the glued addition morphism
-- statement:
--   Let $R$ be a Noetherian commutative integral domain and $W$ a Weierstrass curve over $R$, and write $E = \mathrm{Proj}$ of the graded quotient ring attached to the homogeneous cubic ideal of `W.toProjective`, with structure morphism $\pi =$ `projModelStrCR W.toProjective` $: E \to \operatorname{Spec} R$ (the canonical map to $\operatorname{Spec}$ of the degree-zero part, followed by $\operatorname{Spec}$ of $R \to \mathcal{A}_0$). Assume: $\pi$ is smooth and geometrically integral; the discriminant $W.\Delta$ is a unit in $R$; `hcov`, that for all $i,j \in \mathbf{Z}/3$ the six elements `kw_lrSixU W i j` (the three chart and three symmetric-chart units) generate the unit ideal of $\mathcal{A}_i \otimes_R \mathcal{A}_j$; `hcompat`, that for all $i,j$ and all two of the six indices the associated morphisms to $E$ on the localisations agree after pulling back along the two localisation maps to $\operatorname{Spec}(\mathcal{A}_i \otimes_R \mathcal{A}_j)$; `houter`, the analogous compatibility of the morphisms `kw_lrOuter_toE` on overlaps of the product open cover `kwProjPullbackOpenCoverCR` of $E \times_{\operatorname{Spec} R} E$; and `hnego`, that the negation morphism $\nu =$ `kw_lrAddNegDiag_negMor W` (the $\mathrm{Proj}$ map of the graded involution) satisfies $\pi \circ \nu = \pi$. Then the morphism $E \to E \times_{\operatorname{Spec} R} E$ with components $\nu$ and $\mathrm{id}_E$, followed by the glued addition morphism `kw_lrAddMorphism W hcov hcompat houter`, equals $\pi$ followed by the zero section `(kwZeroSect R W).1` (evaluation of the $Y$-chart at the point at infinity).
--
--   This is the inverse law $P + (-P) = O$ for the addition morphism on the projective Weierstrass model glued from the Lange–Ruppert type system of addition laws, with the Weierstrass involution serving as the inverse. It is one of the group-law axioms consumed by [`WeierstrassProjModel.relativeGroupLaw_exists_of_gluing`](thm.html#WeierstrassProjModel.relativeGroupLaw_exists_of_gluing), which assembles the relative group scheme structure on the smooth model over a base where the discriminant is invertible.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_addMorphism_negMor_mul.lean

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Integral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.addMorphism_negMor_mul.{u} {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (W : WeierstrassCurve R)
    (hsm : Smooth (projModelStrCR W.toProjective))
    (hgi : GeometricallyIntegral (projModelStrCR W.toProjective)) (hΔ : IsUnit W.Δ)
    (hcov : KwLRSixUCoverage W) (hcompat : KwLRPerChartCompat W) (houter : KwLROuterCompat W)
    (hnego : kw_lrAddNegDiag_negMor W ≫ projModelStrCR W.toProjective = projModelStrCR W.toProjective) :
    pullback.lift (kw_lrAddNegDiag_negMor W) (𝟙 (projModelCR W.toProjective))
        (by rw [hnego, Category.id_comp])
      ≫ kw_lrAddMorphism W hcov hcompat houter
    = projModelStrCR W.toProjective ≫ (kwZeroSect R W).1 := by sorry
