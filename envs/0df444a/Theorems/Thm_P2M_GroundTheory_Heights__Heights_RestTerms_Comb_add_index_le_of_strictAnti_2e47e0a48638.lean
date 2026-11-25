-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_add_index_le_of_strictAnti_2e47e0a48638
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_add_index_le_of_strictAnti_2e47e0a48638
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:05:04.543434+00:00
-- url     : https://prove2.me/theorems/4047ca46-f9a8-4b2d-9014-522528d115f1
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb add index le of strict Anti 2e47e0a48638: P2 M Ground Theory Heights  Heights Rest Terms Comb add index le of strict Anti 2e47e0a48638
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb add index le of strict Anti 2e47e0a48638 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb add index le of strict Anti 2e47e0a48638 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCombSortShift.lean#L11-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCombSortShift.lean#L11-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombSortShift
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
open Finset Equiv
open GroundTheory.Heights₂.Heights.RestTerms.Comb

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_add_index_le_of_strictAnti_2e47e0a48638 {m : ℕ} {f : Fin m → ℕ} (hf : StrictAnti f) (a b : Fin m)
    (hab : a ≤ b) : f b + (b : ℕ) ≤ f a + (a : ℕ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«add_index_le_of_strictAnti» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_add_index_le_of_strictAnti_2e47e0a48638
