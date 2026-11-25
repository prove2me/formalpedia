-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ChartComparison_proof_cb37c5d74969
-- name    : P2M_GroundTheory_Heights__Heights_Regular_ChartComparison_proof_cb37c5d74969
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:25:11.375415+00:00
-- url     : https://prove2.me/theorems/ced876fb-bdc4-57fb-971f-20618b8ff661
-- title:
--   P2 M Ground Theory Heights  Heights Regular Chart Comparison proof cb37c5d74969: P2 M Ground Theory Heights  Heights Regular Chart Comparison proof cb37c5d74969
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Chart Comparison proof cb37c5d74969 construction uses the P2 M Ground Theory Heights  Heights Regular Chart Comparison proof cb37c5d74969 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PChartComparison.lean#L28-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PChartComparison.lean#L28-L196

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsTruncPsh
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsTruncTransfer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PChartComparison
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_polyMax_le__638c0d78514a
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_polyMax_mono__555a93f5b347
import Theorems.Thm_ReciprocityTheory_AnForm_A_mollify_thm

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
open Metric
open ReciprocityTheory.AnForm.A (polyMax molli mollify_thm polyMax_le' polyMax_mono')
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_ChartComparison_proof_cb37c5d74969 (h0 : MollifiedLowerBound.Statement)
    (h1 : PolyMaxOscillation.Statement) (h2 : PolyMaxLowerBound.Statement)
    (h3 : TruncPsh.Statement) (h4 : TruncTransfer.Statement) : ChartComparison.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«ChartComparison».«proof» := P2M_GroundTheory_Heights__Heights_Regular_ChartComparison_proof_cb37c5d74969
