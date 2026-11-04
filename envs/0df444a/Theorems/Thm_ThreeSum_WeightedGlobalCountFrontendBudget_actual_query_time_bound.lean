-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCountFrontendBudget_actual_query_time_bound
-- name    : ThreeSum.WeightedGlobalCountFrontendBudget.actual_query_time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:20:15.417792+00:00
-- url     : https://prove2.me/theorems/76ce285b-5760-4149-b878-420d03f1123b
-- title:
--   Weighted Global Count Frontend Budget: actual query time bound
-- statement:
--   The Weighted Global Count Frontend Budget construction uses the actual query time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/CountFrontendBudget.lean#L61-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/CountFrontendBudget.lean#L61-L66

import Definitions.Def_Submission_Weighted_PreparedBudget
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Definitions.Def_Submission_Weighted_Global_CountFrontendBudget
import Theorems.Thm_ThreeSum_WeightedQueryBudget_actual_query_time_bound

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCountFrontendBudget
open Filter Real Asymptotics
open TernaryJointType WeightedGlobalBank WeightedGlobalParameters WeightedGlobalDimensionBounds
open WeightedGlobalEntropyRates WeightedGlobalLocalParameters WeightedGlobalCoverScale WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalCoverCapParameters
open WeightedGlobalOversizeOverhead WeightedGlobalOversizeDimensions WeightedGlobalPrincipalDimensions
open LightWeightedNearPair
open scoped Topology
set_option maxHeartbeats 5000000
set_option maxRecDepth 16000

theorem ThreeSum.WeightedGlobalCountFrontendBudget.actual_query_time_bound {m j L : ℕ} (Q : TritWord (fixedLength (j*m)))
    (hQ : HasType Q (fixedPi (j*m))) :
    (LightWeightedFrozenQuery.queryTime L (bankCut m j) (fixedLength (j*m)) Q : ℝ)≤
      10000*((fixedLength (j*m) : ℝ)+L+1)*((fixedLength (j*m) : ℝ)+1)*envelope m j := by sorry
