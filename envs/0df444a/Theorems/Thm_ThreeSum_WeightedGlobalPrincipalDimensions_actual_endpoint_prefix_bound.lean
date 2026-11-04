-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPrincipalDimensions_actual_endpoint_prefix_bound
-- name    : ThreeSum.WeightedGlobalPrincipalDimensions.actual_endpoint_prefix_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:56:02.570759+00:00
-- url     : https://prove2.me/theorems/dfb6c482-8ec0-4725-90aa-384966ac0693
-- title:
--   Weighted Global Principal Dimensions: actual endpoint prefix bound
-- statement:
--   The Weighted Global Principal Dimensions construction uses the actual endpoint prefix bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrincipalDimensions.lean#L98-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrincipalDimensions.lean#L98-L107

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_Submission_Weighted_Global_TernaryPrincipalDimensions
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPrincipalDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalDimensionBounds
open WeightedGlobalCoverScale WeightedGlobalLocalParameters WeightedGlobalFiniteLedger

theorem ThreeSum.WeightedGlobalPrincipalDimensions.actual_endpoint_prefix_bound {m n j : ℕ} (hm : 0 < m) (hn : 1 < n)
    (hj : j ≤ radixLength m n) :
    (endpointSize m : ℝ)^j ≤ (endpointSize m : ℝ)*(n : ℝ)^endpointCharge m := by sorry
