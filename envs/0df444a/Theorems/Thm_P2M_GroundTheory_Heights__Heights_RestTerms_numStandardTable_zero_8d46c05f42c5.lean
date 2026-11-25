-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_numStandardTable_zero_8d46c05f42c5
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_numStandardTable_zero_8d46c05f42c5
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:36:35.8938+00:00
-- url     : https://prove2.me/theorems/2ebd605d-9830-4046-967a-e02f77c39f68
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms num Standard Table zero 8d46c05f42c5: P2 M Ground Theory Heights  Heights Rest Terms num Standard Table zero 8d46c05f42c5
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms num Standard Table zero 8d46c05f42c5 construction uses the P2 M Ground Theory Heights  Heights Rest Terms num Standard Table zero 8d46c05f42c5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PHookTableauCount.lean#L28-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PHookTableauCount.lean#L28-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_NumStandardTableEqCardMonotone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHookTableauCount
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_numStandardTable_zero_8d46c05f42c5 (m : ℕ) : numStandardTable (fun _ : Fin m => (0 : ℕ)) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«numStandardTable_zero» := P2M_GroundTheory_Heights__Heights_RestTerms_numStandardTable_zero_8d46c05f42c5
