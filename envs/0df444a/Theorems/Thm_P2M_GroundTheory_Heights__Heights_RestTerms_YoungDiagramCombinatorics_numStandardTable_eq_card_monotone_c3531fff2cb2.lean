-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_YoungDiagramCombinatorics_numStandardTable_eq_card_monotone_c3531fff2cb2
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_YoungDiagramCombinatorics_numStandardTable_eq_card_monotone_c3531fff2cb2
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:36:15.451967+00:00
-- url     : https://prove2.me/theorems/b616e4ee-1473-494d-a7f4-debb4c087304
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Young Diagram Combinatorics num Standard Table eq card monotone c3531fff2cb2: P2 M Ground Theory Heights  Heights Rest Terms Young Diagram Combinatorics
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Young Diagram Combinatorics num Standard Table eq card monotone c3531fff2cb2 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Young Diagram Combinatorics num Standard Table eq card monotone c3531fff2cb2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/NumStandardTableEqCardMonotone.lean#L54-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/NumStandardTableEqCardMonotone.lean#L54-L65

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_YoungDiagramCombinatorics_numStandardTable_eq_card_monotone_c3531fff2cb2 {m : ℕ} (lam : Fin m → ℕ) :
    RestTerms.numStandardTable lam =
      Nat.card {T : RestTerms.youngCells lam ≃ Fin (RestTerms.youngCells lam).card //
        Monotone T} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«YoungDiagramCombinatorics».«numStandardTable_eq_card_monotone» := P2M_GroundTheory_Heights__Heights_RestTerms_YoungDiagramCombinatorics_numStandardTable_eq_card_monotone_c3531fff2cb2
