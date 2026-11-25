-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_hookShape_mem_3f5acd6499d7
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_hookShape_mem_3f5acd6499d7
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:20:06.313078+00:00
-- url     : https://prove2.me/theorems/880504f7-0c07-49f6-91ac-8aaace699fd9
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Hook Sum hook Shape mem 3f5acd6499d7: P2 M Ground Theory Heights  Heights Rest Terms Hook Sum hook Shape mem 3f5acd6499d7
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Hook Sum hook Shape mem 3f5acd6499d7 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Hook Sum hook Shape mem 3f5acd6499d7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PHookCharacterSumIdentity.lean#L61-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PHookCharacterSumIdentity.lean#L61-L68

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_hookShape_mem_3f5acd6499d7 (r k l : ℕ) (hlr : l < r) (hlk : l < k) :
    hookShape r k l ∈ partitionsOf r k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«HookSum».«hookShape_mem» := P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_hookShape_mem_3f5acd6499d7
