-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogDetGramDeriv_proof_744363b5faa9
-- name    : P2M_GroundTheory_Heights__Heights_LogDetGramDeriv_proof_744363b5faa9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:54.055194+00:00
-- url     : https://prove2.me/theorems/7d8110c8-4330-494c-9857-f42fc330ade0
-- title:
--   P2 M Ground Theory Heights  Heights Log Det Gram Deriv proof 744363b5faa9: P2 M Ground Theory Heights  Heights Log Det Gram Deriv proof 744363b5faa9
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Det Gram Deriv proof 744363b5faa9 construction uses the P2 M Ground Theory Heights  Heights Log Det Gram Deriv proof 744363b5faa9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PLogDetGramDeriv.lean#L74-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PLogDetGramDeriv.lean#L74-L109

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PLogDetGramDeriv
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
open Matrix
noncomputable section
open MCLogDetGramDeriv

theorem P2M_GroundTheory_Heights__Heights_LogDetGramDeriv_proof_744363b5faa9 (h₁ : InvEntryBound.Statement) (h₂ : InvEntryDeriv.Statement)
    (h₃ : MatrixDetDeriv.Statement) (h₄ : GramEntryDeriv.Statement) :
    LogDetGramDeriv.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogDetGramDeriv».«proof» := P2M_GroundTheory_Heights__Heights_LogDetGramDeriv_proof_744363b5faa9
