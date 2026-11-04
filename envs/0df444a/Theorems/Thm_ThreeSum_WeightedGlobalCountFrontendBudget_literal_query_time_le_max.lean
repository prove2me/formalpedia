-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCountFrontendBudget_literal_query_time_le_max
-- name    : ThreeSum.WeightedGlobalCountFrontendBudget.literal_query_time_le_max
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:20:21.674691+00:00
-- url     : https://prove2.me/theorems/bd21f3cb-cb13-4f2b-b802-108e707e3bac
-- title:
--   Weighted Global Count Frontend Budget: literal query time le max
-- statement:
--   Directly discharges CountFrontend.meets' per-literal-row time premise.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/CountFrontendBudget.lean#L456-L462
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/CountFrontendBudget.lean#L456-L462

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

theorem ThreeSum.WeightedGlobalCountFrontendBudget.literal_query_time_le_max {m j : ℕ} (f g : Config)
    (Q : TritWord (fixedLength (j*m))) (hQ : HasType Q (fixedPi (j*m)))
    (fbase gbase stride tail group : ℕ) :
    LightWeightedPreparedWanted.time
      (LightWeightedWantedRowDispatch.sourceConfig f fbase stride tail group)
      (LightWeightedWantedRowDispatch.sourceConfig g gbase stride tail group) Q≤queryMax m j f g := by sorry
