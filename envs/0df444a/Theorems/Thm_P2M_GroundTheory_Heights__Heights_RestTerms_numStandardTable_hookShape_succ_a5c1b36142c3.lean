-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_numStandardTable_hookShape_succ_a5c1b36142c3
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_numStandardTable_hookShape_succ_a5c1b36142c3
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:36:53.213605+00:00
-- url     : https://prove2.me/theorems/0aaa9d21-f49d-47da-87af-993dea961518
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms num Standard Table hook Shape succ a5c1b36142c3: P2 M Ground Theory Heights  Heights Rest Terms num Standard Table hook Shape succ a5c1b36142c3
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms num Standard Table hook Shape succ a5c1b36142c3 construction uses the P2 M Ground Theory Heights  Heights Rest Terms num Standard Table hook Shape succ a5c1b36142c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PHookTableauCount.lean#L63-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PHookTableauCount.lean#L63-L138

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_numStandardTable_hookShape_succ_a5c1b36142c3 (h : FrobeniusDimensionFormula.Statement) {k l : ℕ}
    (hlk : l < k) : numStandardTable (hookShape (l + 1) k l) = Nat.choose (k - 1) l := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«numStandardTable_hookShape_succ» := P2M_GroundTheory_Heights__Heights_RestTerms_numStandardTable_hookShape_succ_a5c1b36142c3
