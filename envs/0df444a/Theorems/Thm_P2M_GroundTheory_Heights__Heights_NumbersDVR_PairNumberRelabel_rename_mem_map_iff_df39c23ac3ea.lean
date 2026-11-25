-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_rename_mem_map_iff_df39c23ac3ea
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_rename_mem_map_iff_df39c23ac3ea
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:01:03.968111+00:00
-- url     : https://prove2.me/theorems/b84ca36b-ae08-495e-a460-c24e4a942e21
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel rename mem map iff df39c23ac3ea: P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel rename mem map iff df39c23ac3ea
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel rename mem map iff df39c23ac3ea construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel rename mem map iff df39c23ac3ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberRelabel.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberRelabel.lean#L32-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairNumberRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_IntNumRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberRelabel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberRelabel
variable {K₁ K₂ : Type} {ι₁ : K₁ → Type} {ι₂ : K₂ → Type} {R : Type} [CommRing R]
  (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k))

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_rename_mem_map_iff_df39c23ac3ea (I : Ideal (MRing ι₁ R)) (x : MRing ι₁ R) :
    rename σ x ∈ I.map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R) ↔ x ∈ I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«PairNumberRelabel».«rename_mem_map_iff» := P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_rename_mem_map_iff_df39c23ac3ea
