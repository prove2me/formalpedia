-- Prove2me | Theorems.Thm_WeierstrassProjModel_addMorphism_over
-- name    : WeierstrassProjModel.addMorphism_over
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/82c3e99a-290e-509b-87d2-29194684f019
-- title:
--   Glued addition morphism on the projective model lies over the base
-- statement:
--   Let $R$ be a commutative ring and $W$ a Weierstrass curve over $R$, and write $E := \mathrm{Proj}$ of the grading `projModelGradingCR W.toProjective` on the quotient of the homogeneous coordinate ring of $\mathbb{P}^2_R$ by the cubic ideal of $W$, with structure morphism $\pi :=$ `projModelStrCR W.toProjective`, namely `Proj.toSpecZero` followed by the map of spectra induced by $R \to$ (degree-zero part). Three hypotheses are assumed: `hcov : KwLRSixUCoverage W`, asserting that for all $i, j \in \mathrm{Fin}\,3$ the six elements `kw_lrSixU W i j` (the chart and symmetric-chart elements `kw_lrChart_u`, `kw_lrSymChart_u`) generate the unit ideal of $\mathcal{A}_i \otimes_R \mathcal{A}_j$; `hcompat : KwLRPerChartCompat W`, asserting that for all $i, j$ and all $l, l'$ the two maps `kw_lrSixU_toE` agree after pulling back along the localisation maps `kw_lrSixU_locMap`; and `houter : KwLROuterCompat W`, asserting that the per-chart maps `kw_lrOuter_toE` agree on all pairwise overlaps of the open cover `kwProjPullbackOpenCoverCR` of $E \times_{\mathrm{Spec}\,R} E$. The conclusion is that the glued morphism `kw_lrAddMorphism W hcov hcompat houter` $: E \times_{\mathrm{Spec}\,R} E \to E$ followed by $\pi$ equals `pullback.fst` followed by $\pi$.
--
--   This records that the addition law constructed by gluing the chord and symmetric addition laws over the charts of the projective Weierstrass model is a morphism of schemes over $\mathrm{Spec}\,R$, the base being identified through the first projection of the fibre product. It is used by the subsequent verifications of the group-law axioms for this model, [`WeierstrassProjModel.addMorphism_assoc`](thm.html#WeierstrassProjModel.addMorphism_assoc), [`WeierstrassProjModel.addMorphism_comm`](thm.html#WeierstrassProjModel.addMorphism_comm) and [`WeierstrassProjModel.addMorphism_mul_zeroSect`](thm.html#WeierstrassProjModel.addMorphism_mul_zeroSect).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_addMorphism_over.lean

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.addMorphism_over.{u} {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (hcov : KwLRSixUCoverage W) (hcompat : KwLRPerChartCompat W) (houter : KwLROuterCompat W) :
    kw_lrAddMorphism W hcov hcompat houter ≫ projModelStrCR W.toProjective
      = pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
          ≫ projModelStrCR W.toProjective := by sorry
