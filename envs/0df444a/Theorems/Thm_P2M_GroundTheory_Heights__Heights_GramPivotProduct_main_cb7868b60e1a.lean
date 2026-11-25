-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GramPivotProduct_main_cb7868b60e1a
-- name    : P2M_GroundTheory_Heights__Heights_GramPivotProduct_main_cb7868b60e1a
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:44.407456+00:00
-- url     : https://prove2.me/theorems/fe54d6bb-3566-4de3-9ca5-8d3995003a13
-- title:
--   P2 M Ground Theory Heights  Heights Gram Pivot Product main cb7868b60e1a: P2 M Ground Theory Heights  Heights Gram Pivot Product main cb7868b60e1a
-- statement:
--   The P2 M Ground Theory Heights  Heights Gram Pivot Product main cb7868b60e1a construction uses the P2 M Ground Theory Heights  Heights Gram Pivot Product main cb7868b60e1a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PGramPivotProduct.lean#L41-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PGramPivotProduct.lean#L41-L139

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PGramPivotProduct
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
open GroundTheory.Heights₂.Heights.GramPivotProduct

theorem P2M_GroundTheory_Heights__Heights_GramPivotProduct_main_cb7868b60e1a (hLL : LeadMinorLeading.Statement) (hLB : LeadMinorBasic.Statement)
    (hPL : PivotLast.Statement) (hU : UnimodularLast.Statement) (hSD : SchurDetBound.Statement)
    (hQ : IntGramQf.Statement) (hUni : IntGramUnimodular.Statement)
    (hDrop : IntGramDropLast.Statement) (hSub : IntGramSubLast.Statement) :
    GramPivotProduct.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GramPivotProduct».«main» := P2M_GroundTheory_Heights__Heights_GramPivotProduct_main_cb7868b60e1a
