-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCountFrontendBudget_exists_fixed_block
-- name    : ThreeSum.WeightedGlobalCountFrontendBudget.exists_fixed_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:20:24.211648+00:00
-- url     : https://prove2.me/theorems/c4456778-9f5b-49cb-a1f3-2126cbf08b4e
-- title:
--   Weighted Global Count Frontend Budget: exists fixed block
-- statement:
--   The same fixed block satisfies the actual cardinality rates and the
--   small repeated-family overhead required above.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/CountFrontendBudget.lean#L438-L443
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/CountFrontendBudget.lean#L438-L443

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

theorem ThreeSum.WeightedGlobalCountFrontendBudget.exists_fixed_block {K : ℕ} (hK : 100000000000000000000≤K) (c d minimum : ℕ) :
    ∃ m, minimum≤m ∧ GoodBlock K m ∧
      overheadCharge (selectedMoment K) c d m<microAllowance K ∧
      principalExponent K (selectedMoment K) c d m<frontendExponent := by sorry
