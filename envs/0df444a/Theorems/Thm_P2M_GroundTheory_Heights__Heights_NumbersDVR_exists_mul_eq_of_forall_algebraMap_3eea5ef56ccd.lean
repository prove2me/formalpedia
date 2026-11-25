-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_mul_eq_of_forall_algebraMap_3eea5ef56ccd
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_mul_eq_of_forall_algebraMap_3eea5ef56ccd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:10:34.873906+00:00
-- url     : https://prove2.me/theorems/da4d062b-d5de-4c0b-8a9b-2d921308204e
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR exists mul eq of forall algebra Map 3eea5ef56ccd: P2 M Ground Theory Heights  Heights Numbers DVR exists mul eq of forall algebra Map 3eea5ef56ccd
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR exists mul eq of forall algebra Map 3eea5ef56ccd construction uses the P2 M Ground Theory Heights  Heights Numbers DVR exists mul eq of forall algebra Map 3eea5ef56ccd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpLocalChart.lean#L71-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpLocalChart.lean#L71-L82

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpOrderLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpLocalChart
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
universe u
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_mul_eq_of_forall_algebraMap_3eea5ef56ccd {B X : Type*} [CommRing B] [CommRing X] (W : Ideal B) [W.IsPrime]
    (φ : X →+* Localization.AtPrime W) (h : ∀ z, ∃ a, φ a = algebraMap B (Localization.AtPrime W) z)
    (d : Localization.AtPrime W) :
    ∃ a b, φ b ∉ IsLocalRing.maximalIdeal (Localization.AtPrime W) ∧ φ b * d = φ a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«exists_mul_eq_of_forall_algebraMap» := P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_mul_eq_of_forall_algebraMap_3eea5ef56ccd
