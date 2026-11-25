-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_numStandardTable_pos_e362a1d9e1a0
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_numStandardTable_pos_e362a1d9e1a0
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:36:26.563794+00:00
-- url     : https://prove2.me/theorems/776b54d6-12da-4f28-a121-266940075876
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms num Standard Table pos e362a1d9e1a0: P2 M Ground Theory Heights  Heights Rest Terms num Standard Table pos e362a1d9e1a0
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms num Standard Table pos e362a1d9e1a0 construction uses the P2 M Ground Theory Heights  Heights Rest Terms num Standard Table pos e362a1d9e1a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/NumStandardTablePos.lean#L9-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/NumStandardTablePos.lean#L9-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_NumStandardTablePos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open Finset

theorem P2M_GroundTheory_Heights__Heights_RestTerms_numStandardTable_pos_e362a1d9e1a0 {m : ℕ} (lam : Fin m → ℕ) : 0 < numStandardTable lam := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«numStandardTable_pos» := P2M_GroundTheory_Heights__Heights_RestTerms_numStandardTable_pos_e362a1d9e1a0
