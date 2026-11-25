-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_YoungDiagramCombinatorics_shapeCells_hookShape_f3858b8d382d
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_YoungDiagramCombinatorics_shapeCells_hookShape_f3858b8d382d
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:36:15.232621+00:00
-- url     : https://prove2.me/theorems/6f692407-63d9-4191-87cc-c90d3a43add0
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Young Diagram Combinatorics shape Cells hook Shape f3858b8d382d: P2 M Ground Theory Heights  Heights Rest Terms Young Diagram Combinatorics shape Cells h
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Young Diagram Combinatorics shape Cells hook Shape f3858b8d382d construction uses the P2 M Ground Theory Heights  Heights Rest Terms Young Diagram Combinatorics shape Cells hook Shape f3858b8d382d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/NumStandardTableEqCardMonotone.lean#L75-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/NumStandardTableEqCardMonotone.lean#L75-L90

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_YoungDiagramCombinatorics_shapeCells_hookShape_f3858b8d382d (r k b : ℕ) (hb : b < r) :
    IndefiniteRowSideFullHecke.RestTerms.shapeCells (IndefiniteRowSideFullHecke.RestTerms.hookShape k b) =
      IndefiniteRowSideFullHecke.RestTerms.shapeCells (RestTerms.hookShape r k b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«YoungDiagramCombinatorics».«shapeCells_hookShape» := P2M_GroundTheory_Heights__Heights_RestTerms_YoungDiagramCombinatorics_shapeCells_hookShape_f3858b8d382d
