-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_YoungDiagramCombinatorics_numSYT_eq_5bfc4600f427
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_YoungDiagramCombinatorics_numSYT_eq_5bfc4600f427
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:36:09.343401+00:00
-- url     : https://prove2.me/theorems/8e1a155b-20c5-5514-83b2-94a7f5762dac
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Young Diagram Combinatorics num SYT eq 5bfc4600f427: P2 M Ground Theory Heights  Heights Rest Terms Young Diagram Combinatorics num SYT eq 5bfc4600f427
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Young Diagram Combinatorics num SYT eq 5bfc4600f427 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Young Diagram Combinatorics num SYT eq 5bfc4600f427 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/NumStandardTableEqCardMonotone.lean#L67-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/NumStandardTableEqCardMonotone.lean#L67-L73

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_YoungDiagramCombinatorics_numSYT_eq_5bfc4600f427 {r : ℕ} (la : Fin r → ℕ) :
    IndefiniteRowSideFullHecke.RestTerms.numSYT la = RestTerms.numStandardTable la := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«YoungDiagramCombinatorics».«numSYT_eq» := P2M_GroundTheory_Heights__Heights_RestTerms_YoungDiagramCombinatorics_numSYT_eq_5bfc4600f427
