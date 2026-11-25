-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_hook_classification_668125ac27af
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_hook_classification_668125ac27af
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:20:23.265025+00:00
-- url     : https://prove2.me/theorems/3560f9af-385a-4b7f-9cca-5141290e265f
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Hook Sum hook classification 668125ac27af: P2 M Ground Theory Heights  Heights Rest Terms Hook Sum hook classification 668125ac27af
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Hook Sum hook classification 668125ac27af construction uses the P2 M Ground Theory Heights  Heights Rest Terms Hook Sum hook classification 668125ac27af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PHookCharacterSumIdentity.lean#L75-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PHookCharacterSumIdentity.lean#L75-L159

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_hook_classification_668125ac27af {r k : ℕ} (hk : 1 ≤ k) {nu : Fin r → ℕ}
    (hnu : nu ∈ partitionsOf r k) (hh : ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1) {l : ℕ}
    (hl : (Finset.univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ nu i = 1).card = l) :
    l < r ∧ l < k ∧ hookShape r k l = nu := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«HookSum».«hook_classification» := P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_hook_classification_668125ac27af
