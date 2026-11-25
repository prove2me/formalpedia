-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_YoungDiagramCombinatorics_numSYT_hookShape_4cc1d79bbf5a
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_YoungDiagramCombinatorics_numSYT_hookShape_4cc1d79bbf5a
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:36:20.092855+00:00
-- url     : https://prove2.me/theorems/ee49e35c-1cf5-4a5f-a637-3c4ecd1f435b
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Young Diagram Combinatorics num SYT hook Shape 4cc1d79bbf5a: P2 M Ground Theory Heights  Heights Rest Terms Young Diagram Combinatorics num SYT hook Shap
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Young Diagram Combinatorics num SYT hook Shape 4cc1d79bbf5a construction uses the P2 M Ground Theory Heights  Heights Rest Terms Young Diagram Combinatorics num SYT hook Shape 4cc1d79bbf5a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/NumStandardTableEqCardMonotone.lean#L92-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/NumStandardTableEqCardMonotone.lean#L92-L97

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_YoungDiagramCombinatorics_numSYT_hookShape_4cc1d79bbf5a (r k b : ℕ) (hb : b < r) :
    IndefiniteRowSideFullHecke.RestTerms.numSYT (IndefiniteRowSideFullHecke.RestTerms.hookShape k b) =
      RestTerms.numStandardTable (RestTerms.hookShape r k b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«YoungDiagramCombinatorics».«numSYT_hookShape» := P2M_GroundTheory_Heights__Heights_RestTerms_YoungDiagramCombinatorics_numSYT_hookShape_4cc1d79bbf5a
