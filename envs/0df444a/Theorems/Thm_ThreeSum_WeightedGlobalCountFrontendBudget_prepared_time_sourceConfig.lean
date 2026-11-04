-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCountFrontendBudget_prepared_time_sourceConfig
-- name    : ThreeSum.WeightedGlobalCountFrontendBudget.prepared_time_sourceConfig
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:17:40.332915+00:00
-- url     : https://prove2.me/theorems/5a18a480-7c3d-4c2f-b7d4-0c10b15486ee
-- title:
--   Weighted Global Count Frontend Budget: prepared time source Config
-- statement:
--   Group dispatch changes only source-bank pointers; it leaves the actual
--   prepared-query running-time function unchanged.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/CountFrontendBudget.lean#L448-L453
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/CountFrontendBudget.lean#L448-L453

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

theorem ThreeSum.WeightedGlobalCountFrontendBudget.prepared_time_sourceConfig {N : ℕ} (f g : Config) (Q : TritWord N)
    (fbase gbase stride tail group : ℕ) :
    LightWeightedPreparedWanted.time
      (LightWeightedWantedRowDispatch.sourceConfig f fbase stride tail group)
      (LightWeightedWantedRowDispatch.sourceConfig g gbase stride tail group) Q=
      LightWeightedPreparedWanted.time f g Q := by sorry

attribute [defeq] ThreeSum.WeightedGlobalCountFrontendBudget.prepared_time_sourceConfig
