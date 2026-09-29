-- Prove2me | Theorems.Thm_WeierstrassProjModel_addMorphism_zeroSect_mul
-- name    : WeierstrassProjModel.addMorphism_zeroSect_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/23f99038-476b-53b1-a0a2-477edf09b826
-- title:
--   Left unit law for the glued addition morphism
-- statement:
--   Let $R$ be a Noetherian commutative domain and $W$ a Weierstrass curve over $R$. Write $E := \mathrm{Proj}$ of the graded quotient ring attached to the projective Weierstrass equation of $W$ (`projModelCR W.toProjective`) and $\pi :=$ `projModelStrCR W.toProjective` for its structure morphism to $\operatorname{Spec} R$, obtained from `Proj.toSpecZero` followed by the map induced by $R \to \mathcal{A}_0$. Assume $\pi$ is smooth and geometrically integral, that the discriminant $W.\Delta$ is a unit in $R$, and that the three gluing hypotheses hold: `KwLRSixUCoverage W`, i.e. for all $i,j \in \{0,1,2\}$ the six elements `kw_lrSixU W i j` (three from the chord charts and three from the symmetric charts) generate the unit ideal of $\mathcal{A}_i \otimes_R \mathcal{A}_j$; `KwLRPerChartCompat W`, i.e. for each $i,j$ the six morphisms `kw_lrSixU_toE W i j l` from the corresponding away-localisations to $E$ agree after pulling back along any two of the localisation maps `kw_lrSixU_locMap W i j l`; and `KwLROuterCompat W`, i.e. the resulting per-chart morphisms `kw_lrOuter_toE` agree on all overlaps of the open cover `kwProjPullbackOpenCoverCR` of $\mathrm{pullback}\,\pi\,\pi$. Let $m :=$ `kw_lrAddMorphism W hcov hcompat houter` $: \mathrm{pullback}\,\pi\,\pi \to E$ be the morphism glued from these data, and let $o$ be the zero section `kwZeroSect R W`, a morphism $\operatorname{Spec} R \to E$ with $o \circ \pi = \mathrm{id}$ over $\operatorname{Spec} R$, given on the $X_1$-chart by the evaluation `kwYChartEval` followed by `Proj.awayι`. Then the morphism $E \to \mathrm{pullback}\,\pi\,\pi$ with components $\pi$ followed by $o$, and $\mathrm{id}_E$, composed with $m$, equals $\mathrm{id}_E$. The compatibility condition required by `pullback.lift` is discharged inside the statement from $o \circ \pi = \mathrm{id}$ by the category axioms.
--
--   This is the left unit law $m(o(\pi(x)),x) = x$ for the addition morphism of the projective Weierstrass model, one of the group-law axioms verified scheme-theoretically for the glued chord-and-symmetric addition laws. It is used by [`WeierstrassProjModel.relativeGroupLaw_exists_of_gluing`](thm.html#WeierstrassProjModel.relativeGroupLaw_exists_of_gluing), which assembles the axioms into a relative group law on the model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_addMorphism_zeroSect_mul.lean

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Integral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.addMorphism_zeroSect_mul.{u} {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (W : WeierstrassCurve R)
    (hsm : Smooth (projModelStrCR W.toProjective))
    (hgi : GeometricallyIntegral (projModelStrCR W.toProjective)) (hΔ : IsUnit W.Δ)
    (hcov : KwLRSixUCoverage W) (hcompat : KwLRPerChartCompat W) (houter : KwLROuterCompat W) :
    pullback.lift (projModelStrCR W.toProjective ≫ (kwZeroSect R W).1) (𝟙 (projModelCR W.toProjective))
        (by rw [Category.assoc, (kwZeroSect R W).2, Category.comp_id, Category.id_comp])
      ≫ kw_lrAddMorphism W hcov hcompat houter = 𝟙 (projModelCR W.toProjective) := by sorry
