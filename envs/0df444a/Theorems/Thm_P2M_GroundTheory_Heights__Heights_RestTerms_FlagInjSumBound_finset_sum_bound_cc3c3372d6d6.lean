-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagInjSumBound_finset_sum_bound_cc3c3372d6d6
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_FlagInjSumBound_finset_sum_bound_cc3c3372d6d6
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:19:21.748997+00:00
-- url     : https://prove2.me/theorems/9d2b6dd3-65eb-5560-b925-e705655a1c33
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag Inj Sum Bound finset sum bound cc3c3372d6d6: P2 M Ground Theory Heights  Heights Rest Terms Flag Inj Sum Bound finset sum bound cc3c3372d6d6
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag Inj Sum Bound finset sum bound cc3c3372d6d6 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag Inj Sum Bound finset sum bound cc3c3372d6d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFlagInjSumBound.lean#L9-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFlagInjSumBound.lean#L9-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagInjSumBound
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_FlagInjSumBound_finset_sum_bound_cc3c3372d6d6 (S : Finset ℕ) :
    ∑ i ∈ Finset.range S.card, i ≤ ∑ x ∈ S, x ∧
      (∑ x ∈ S, x = ∑ i ∈ Finset.range S.card, i → S ⊆ Finset.range S.card) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«FlagInjSumBound».«finset_sum_bound» := P2M_GroundTheory_Heights__Heights_RestTerms_FlagInjSumBound_finset_sum_bound_cc3c3372d6d6
