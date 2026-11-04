-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCountFrontendBudget_actual_query_envelope_volume
-- name    : ThreeSum.WeightedGlobalCountFrontendBudget.actual_query_envelope_volume
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:18:12.160968+00:00
-- url     : https://prove2.me/theorems/5b2a115b-10ef-488b-9be5-1bba28dca0ce
-- title:
--   Weighted Global Count Frontend Budget: actual query envelope volume
-- statement:
--   This prices the actual full inverse-query envelope, not just near leaves.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/CountFrontendBudget.lean#L89-L120
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/CountFrontendBudget.lean#L89-L120

import Definitions.Def_Submission_Weighted_PreparedBudget
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Definitions.Def_Submission_Weighted_Global_CountFrontendBudget
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

theorem ThreeSum.WeightedGlobalCountFrontendBudget.actual_query_envelope_volume {K m n j : ℕ} (hK : 0<K) (hm : 0<m) (hn : 1<n)
    (hj : j≤radixLength m n) :
    (n : ℝ)*((nativePrime K m : ℝ)/partitionCap m)^j*(inflation K m : ℝ)^(4*j)*envelope m j≤
      (Real.exp (WeightedGlobalOversizeDimensions.querySlope K m)/z^1024)*(n : ℝ)^WeightedGlobalOversizeRates.queryCharge K m := by sorry
