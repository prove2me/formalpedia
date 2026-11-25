-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_card_hookShape_20885ef91065
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_card_hookShape_20885ef91065
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:20:10.343817+00:00
-- url     : https://prove2.me/theorems/3aa19eae-8a74-4be0-a838-f61872b5fa47
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Hook Sum card hook Shape 20885ef91065: P2 M Ground Theory Heights  Heights Rest Terms Hook Sum card hook Shape 20885ef91065
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Hook Sum card hook Shape 20885ef91065 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Hook Sum card hook Shape 20885ef91065 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PHookCharacterSumIdentity.lean#L27-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PHookCharacterSumIdentity.lean#L27-L39

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_card_hookShape_20885ef91065 (r k l : ℕ) (hl : l < r) :
    (Finset.univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ hookShape r k l i = 1).card = l := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«HookSum».«card_hookShape» := P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_card_hookShape_20885ef91065
