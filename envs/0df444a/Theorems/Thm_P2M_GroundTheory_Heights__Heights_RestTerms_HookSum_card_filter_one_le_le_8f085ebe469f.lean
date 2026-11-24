-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_card_filter_one_le_le_8f085ebe469f
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_card_filter_one_le_le_8f085ebe469f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:08.384173+00:00
-- url     : https://prove2.me/theorems/f0890b07-fd62-49f9-8761-ff1d6e6ffb87
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Hook Sum card filter one le le 8f085ebe469f: P2 M Ground Theory Heights  Heights Rest Terms Hook Sum card filter one le le 8f085ebe469f
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Hook Sum card filter one le le 8f085ebe469f construction uses the P2 M Ground Theory Heights  Heights Rest Terms Hook Sum card filter one le le 8f085ebe469f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PHookCharacterSumIdentity.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PHookCharacterSumIdentity.lean#L18-L25

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_card_filter_one_le_le_8f085ebe469f (r m : ℕ) (hm : m < r) :
    (Finset.univ.filter fun j : Fin r => 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ m).card = m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«HookSum».«card_filter_one_le_le» := P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_card_filter_one_le_le_8f085ebe469f
