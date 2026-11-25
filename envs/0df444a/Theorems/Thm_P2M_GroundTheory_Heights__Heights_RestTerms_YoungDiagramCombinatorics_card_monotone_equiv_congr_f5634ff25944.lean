-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_YoungDiagramCombinatorics_card_monotone_equiv_congr_f5634ff25944
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_YoungDiagramCombinatorics_card_monotone_equiv_congr_f5634ff25944
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:36:05.045843+00:00
-- url     : https://prove2.me/theorems/8c65c2dd-411f-4dfa-a2b8-42d8c12d831d
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Young Diagram Combinatorics card monotone equiv congr f5634ff25944: P2 M Ground Theory Heights  Heights Rest Terms Young Diagram Combinatorics card monot
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Young Diagram Combinatorics card monotone equiv congr f5634ff25944 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Young Diagram Combinatorics card monotone equiv congr f5634ff25944 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/NumStandardTableEqCardMonotone.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/NumStandardTableEqCardMonotone.lean#L11-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_NumStandardTableEqCardMonotone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.YoungDiagramCombinatorics
open MvPolynomial Finset

theorem P2M_GroundTheory_Heights__Heights_RestTerms_YoungDiagramCombinatorics_card_monotone_equiv_congr_f5634ff25944 {α β : Type*} [Preorder α] [Preorder β] (e : α ≃o β)
    {n n' : ℕ} (h : n = n') :
    Nat.card {T : α ≃ Fin n // Monotone T} = Nat.card {T : β ≃ Fin n' // Monotone T} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«YoungDiagramCombinatorics».«card_monotone_equiv_congr» := P2M_GroundTheory_Heights__Heights_RestTerms_YoungDiagramCombinatorics_card_monotone_equiv_congr_f5634ff25944
