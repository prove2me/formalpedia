-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ChartMollifiedBounds_proof_26ceefebb180
-- name    : P2M_GroundTheory_Heights__Heights_Regular_ChartMollifiedBounds_proof_26ceefebb180
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:35:21.056225+00:00
-- url     : https://prove2.me/theorems/18f4b553-791b-4b8e-b0c3-d801c9c910bb
-- title:
--   P2 M Ground Theory Heights  Heights Regular Chart Mollified Bounds proof 26ceefebb180: P2 M Ground Theory Heights  Heights Regular Chart Mollified Bounds proof 26ceefebb180
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Chart Mollified Bounds proof 26ceefebb180 construction uses the P2 M Ground Theory Heights  Heights Regular Chart Mollified Bounds proof 26ceefebb180 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PChartMollifiedBounds.lean#L53-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PChartMollifiedBounds.lean#L53-L109

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsChartBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsTruncPsh
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PChartMollifiedBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology MeasureTheory Set
open ReciprocityTheory.AnForm.A (IsPsh Mollifier molli coordDiv limsupExt polyMax shrink)
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_ChartMollifiedBounds_proof_26ceefebb180 (h : TruncPsh.Statement) : ChartMollifiedBounds.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«ChartMollifiedBounds».«proof» := P2M_GroundTheory_Heights__Heights_Regular_ChartMollifiedBounds_proof_26ceefebb180
