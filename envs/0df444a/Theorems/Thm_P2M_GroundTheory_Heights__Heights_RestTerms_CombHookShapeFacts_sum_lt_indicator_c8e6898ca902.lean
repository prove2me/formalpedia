-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CombHookShapeFacts_sum_lt_indicator_c8e6898ca902
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_CombHookShapeFacts_sum_lt_indicator_c8e6898ca902
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:04:25.221038+00:00
-- url     : https://prove2.me/theorems/665725d1-3fe1-4e20-a77a-b02352c612f8
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb Hook Shape Facts sum lt indicator c8e6898ca902: P2 M Ground Theory Heights  Heights Rest Terms Comb Hook Shape Facts sum lt indicator c8e6898ca902
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb Hook Shape Facts sum lt indicator c8e6898ca902 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb Hook Shape Facts sum lt indicator c8e6898ca902 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCombHookShapeFacts.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCombHookShapeFacts.lean#L9-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombHookShapeFacts
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_CombHookShapeFacts_sum_lt_indicator_c8e6898ca902 (l : ℕ) :
    ∀ m : ℕ, (∑ i ∈ range m, if i < l then 1 else 0) = min m l := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«CombHookShapeFacts».«sum_lt_indicator» := P2M_GroundTheory_Heights__Heights_RestTerms_CombHookShapeFacts_sum_lt_indicator_c8e6898ca902
