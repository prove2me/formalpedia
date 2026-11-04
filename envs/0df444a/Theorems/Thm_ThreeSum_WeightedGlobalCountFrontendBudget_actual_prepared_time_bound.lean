-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCountFrontendBudget_actual_prepared_time_bound
-- name    : ThreeSum.WeightedGlobalCountFrontendBudget.actual_prepared_time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:44:21.955717+00:00
-- url     : https://prove2.me/theorems/34494937-f237-43ec-b11d-5691a07b1b9f
-- title:
--   Weighted Global Count Frontend Budget: actual prepared time bound
-- statement:
--   The Weighted Global Count Frontend Budget construction uses the actual prepared time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/CountFrontendBudget.lean#L71-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/CountFrontendBudget.lean#L71-L77

import Definitions.Def_Submission_Weighted_PreparedBudget
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Definitions.Def_Submission_Weighted_Global_CountFrontendBudget
import Theorems.Thm_ThreeSum_WeightedPreparedBudget_actual_prepared_time_bound

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

theorem ThreeSum.WeightedGlobalCountFrontendBudget.actual_prepared_time_bound {m j : ℕ} (f g : Config)
    (hT : f.T=bankCut m j) (Q : TritWord (fixedLength (j*m))) (hQ : HasType Q (fixedPi (j*m))) :
    (LightWeightedPreparedWanted.time f g Q : ℝ)≤
      100000*(width (fixedLength (j*m)) f g : ℝ)^3*envelope m j := by sorry
