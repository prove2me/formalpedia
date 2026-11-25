-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_support_log_iSup_place_finite_eb17bd99c37b
-- name    : P2M_GroundTheory_Heights__Heights_support_log_iSup_place_finite_eb17bd99c37b
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:50:49.590552+00:00
-- url     : https://prove2.me/theorems/2b19e652-fea6-4eef-8ff1-191e83417cd1
-- title:
--   P2 M Ground Theory Heights  Heights support log i Sup place finite eb17bd99c37b: P2 M Ground Theory Heights  Heights support log i Sup place finite eb17bd99c37b
-- statement:
--   The P2 M Ground Theory Heights  Heights support log i Sup place finite eb17bd99c37b construction uses the P2 M Ground Theory Heights  Heights support log i Sup place finite eb17bd99c37b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FieldChange.lean#L164-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FieldChange.lean#L164-L170

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardEmbeddingsRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField Module
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_support_log_iSup_place_finite_eb17bd99c37b {F : Type*} [Field F] [NumberField F] {ι : Type*} [Finite ι]
    {y : ι → F} (hy : y ≠ 0) :
    (Function.support fun w : FinitePlace F ↦ Real.log (⨆ i, w (y i))).Finite := by sorry

alias «GroundTheory».«Heights₂».«Heights».«support_log_iSup_place_finite» := P2M_GroundTheory_Heights__Heights_support_log_iSup_place_finite_eb17bd99c37b
