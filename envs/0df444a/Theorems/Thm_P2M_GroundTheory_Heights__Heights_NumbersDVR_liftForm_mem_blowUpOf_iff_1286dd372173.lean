-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_mem_blowUpOf_iff_1286dd372173
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_mem_blowUpOf_iff_1286dd372173
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:12:12.715364+00:00
-- url     : https://prove2.me/theorems/af98bbe0-39a8-465f-b1ec-8fd557731e29
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR lift Form mem blow Up Of iff 1286dd372173: P2 M Ground Theory Heights  Heights Numbers DVR lift Form mem blow Up Of iff 1286dd372173
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR lift Form mem blow Up Of iff 1286dd372173 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR lift Form mem blow Up Of iff 1286dd372173 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpLocalChart.lean#L94-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpLocalChart.lean#L94-L97

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
variable {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_mem_blowUpOf_iff_1286dd372173 (P : Ideal (MRing ι R)) (u : J → MRing ι R) (p : MRing ι R) :
    liftForm p ∈ blowUpOf P u ↔ p ∈ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«liftForm_mem_blowUpOf_iff» := P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_mem_blowUpOf_iff_1286dd372173
