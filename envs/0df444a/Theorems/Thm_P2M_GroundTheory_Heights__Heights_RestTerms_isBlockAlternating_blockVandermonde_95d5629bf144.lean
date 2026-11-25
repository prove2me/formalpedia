-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_isBlockAlternating_blockVandermonde_95d5629bf144
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_isBlockAlternating_blockVandermonde_95d5629bf144
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:36:41.65942+00:00
-- url     : https://prove2.me/theorems/1bf6bab6-e041-5677-8842-6d6a534e1fd6
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms is Block Alternating block Vandermonde 95d5629bf144: P2 M Ground Theory Heights  Heights Rest Terms is Block Alternating block Vandermonde 95d5629bf144
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms is Block Alternating block Vandermonde 95d5629bf144 construction uses the P2 M Ground Theory Heights  Heights Rest Terms is Block Alternating block Vandermonde 95d5629bf144 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/StatementsFlag.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/StatementsFlag.lean#L22-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Inhabitants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
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
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_isBlockAlternating_blockVandermonde_95d5629bf144 (f N : ℕ) :
    IsBlockAlternating f N (blockVandermonde f N) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«isBlockAlternating_blockVandermonde» := P2M_GroundTheory_Heights__Heights_RestTerms_isBlockAlternating_blockVandermonde_95d5629bf144
