-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_exists_hookShape_of_isHook_a343077746e1
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_exists_hookShape_of_isHook_a343077746e1
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:35:43.764006+00:00
-- url     : https://prove2.me/theorems/88ef22af-7cd4-56ff-af10-28dd39b5af19
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms exists hook Shape of is Hook a343077746e1: P2 M Ground Theory Heights  Heights Rest Terms exists hook Shape of is Hook a343077746e1
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms exists hook Shape of is Hook a343077746e1 construction uses the P2 M Ground Theory Heights  Heights Rest Terms exists hook Shape of is Hook a343077746e1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PHookSumBound.lean#L9-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PHookSumBound.lean#L9-L81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHookSumBound
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_exists_hookShape_of_isHook_a343077746e1 {r k : ℕ} (hk : 1 ≤ k) (nu : Fin r → ℕ) (hanti : Antitone nu)
    (hsum : ∑ i, nu i = k) (hhook : ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1) :
    ∃ l, l < r ∧ l < k ∧ nu = hookShape r k l := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«exists_hookShape_of_isHook» := P2M_GroundTheory_Heights__Heights_RestTerms_exists_hookShape_of_isHook_a343077746e1
