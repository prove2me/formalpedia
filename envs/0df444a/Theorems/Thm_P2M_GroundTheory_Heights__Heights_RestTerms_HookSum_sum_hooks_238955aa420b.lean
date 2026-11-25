-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_sum_hooks_238955aa420b
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_sum_hooks_238955aa420b
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:20:20.22201+00:00
-- url     : https://prove2.me/theorems/bdb412a1-5a73-48c9-b214-2dbc362df8bf
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Hook Sum sum hooks 238955aa420b: P2 M Ground Theory Heights  Heights Rest Terms Hook Sum sum hooks 238955aa420b
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Hook Sum sum hooks 238955aa420b construction uses the P2 M Ground Theory Heights  Heights Rest Terms Hook Sum sum hooks 238955aa420b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PHookCharacterSumIdentity.lean#L161-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PHookCharacterSumIdentity.lean#L161-L189

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHookCharacterSumIdentity
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
open GroundTheory.Heights₂.Heights.RestTerms.HookSum

theorem P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_sum_hooks_238955aa420b (r k : ℕ) (hk : 1 ≤ k) (g : (Fin r → ℕ) → ℚ) :
    ∑ nu ∈ partitionsOf r k, g nu *
        (if ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1 then
          (-1 : ℚ) ^ ((Finset.univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ nu i = 1).card)
        else 0) =
      ∑ l ∈ Finset.range (min r k), (-1 : ℚ) ^ l * g (hookShape r k l) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«HookSum».«sum_hooks» := P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_sum_hooks_238955aa420b
