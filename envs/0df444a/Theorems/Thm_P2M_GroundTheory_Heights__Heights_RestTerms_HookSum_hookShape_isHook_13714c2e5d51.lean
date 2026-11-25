-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_hookShape_isHook_13714c2e5d51
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_hookShape_isHook_13714c2e5d51
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:20:16.414989+00:00
-- url     : https://prove2.me/theorems/5a4c44fc-0973-470e-a885-3de54afaa1d9
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Hook Sum hook Shape is Hook 13714c2e5d51: P2 M Ground Theory Heights  Heights Rest Terms Hook Sum hook Shape is Hook 13714c2e5d51
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Hook Sum hook Shape is Hook 13714c2e5d51 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Hook Sum hook Shape is Hook 13714c2e5d51 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PHookCharacterSumIdentity.lean#L70-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PHookCharacterSumIdentity.lean#L70-L73

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_hookShape_isHook_13714c2e5d51 (r k l : ℕ) : ∀ i : Fin r, (i : ℕ) ≠ 0 → hookShape r k l i ≤ 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«HookSum».«hookShape_isHook» := P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_hookShape_isHook_13714c2e5d51
