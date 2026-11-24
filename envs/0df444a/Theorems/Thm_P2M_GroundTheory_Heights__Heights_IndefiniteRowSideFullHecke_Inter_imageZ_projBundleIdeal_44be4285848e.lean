-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_imageZ_projBundleIdeal_44be4285848e
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_imageZ_projBundleIdeal_44be4285848e
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:27:00.833082+00:00
-- url     : https://prove2.me/theorems/a987c102-ed84-4009-8fc2-b22302f1f421
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter image Z proj Bundle Ideal 44be4285848e: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter image Z proj B
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter image Z proj Bundle Ideal 44be4285848e construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter image Z proj Bundle Ideal 44be4285848e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsSmoothHermOfIsPullHermInl.lean#L40-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsSmoothHermOfIsPullHermInl.lean#L40-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ProjLineRankTwoPushforwardHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermTensor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermOfIsPullHermInl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_imageZ_projBundleIdeal_44be4285848e (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    imageZ (inlV (ι₂ := fun _ : Unit => Fin N1)) (projBundleIdeal P B) = P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«imageZ_projBundleIdeal» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_imageZ_projBundleIdeal_44be4285848e
