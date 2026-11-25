-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_isRelevant_map_iff_bbef0f1ec389
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_isRelevant_map_iff_bbef0f1ec389
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:11:46.160914+00:00
-- url     : https://prove2.me/theorems/f6630079-7916-59ec-85a9-8a5a296aa0f5
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel is Relevant map iff bbef0f1ec389: P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel is Relevant map iff bbef0f1ec3
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel is Relevant map iff bbef0f1ec389 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel is Relevant map iff bbef0f1ec389 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberRelabel.lean#L57-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberRelabel.lean#L57-L71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairNumberRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_IntNumRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_isRelevant_map_iff_44c6feca16d0

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
variable (e : K₁ ≃ K₂)

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_isRelevant_map_iff_bbef0f1ec389 (hσ : ∀ v, (σ v).1 = e v.1) (W : Ideal (MRing ι₁ R)) :
    IsRelevant (W.map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R)) ↔ IsRelevant W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«PairNumberRelabel».«isRelevant_map_iff» := P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_isRelevant_map_iff_bbef0f1ec389
