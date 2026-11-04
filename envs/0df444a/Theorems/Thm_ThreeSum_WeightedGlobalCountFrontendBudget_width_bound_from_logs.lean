-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCountFrontendBudget_width_bound_from_logs
-- name    : ThreeSum.WeightedGlobalCountFrontendBudget.width_bound_from_logs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:21:42.93262+00:00
-- url     : https://prove2.me/theorems/54f86795-0a91-4363-85bf-403a2dd47df4
-- title:
--   Weighted Global Count Frontend Budget: width bound from logs
-- statement:
--   Word-value logarithms may depend on the original input size, so they are
--   bounded by the full radix length, uniformly over every prefix.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/CountFrontendBudget.lean#L315-L323
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/CountFrontendBudget.lean#L315-L323

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

theorem ThreeSum.WeightedGlobalCountFrontendBudget.width_bound_from_logs {m n j v : ℕ} (hj : j≤radixLength m n) (f g : Config)
    (hf : f.L≤2*fixedLength (j*m)) (hg : g.L≤2*fixedLength (j*m))
    (hv : Nat.log 2 (f.V+1)+Nat.log 2 (g.V+1)≤v*(radixLength m n+1)) :
    width (fixedLength (j*m)) f g≤(5*fixedLength m+v+3)*(radixLength m n+1) := by sorry
