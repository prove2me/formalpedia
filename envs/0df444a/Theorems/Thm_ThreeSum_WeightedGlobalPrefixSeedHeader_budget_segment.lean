-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPrefixSeedHeader_budget_segment
-- name    : ThreeSum.WeightedGlobalPrefixSeedHeader.budget_segment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:11:17.475568+00:00
-- url     : https://prove2.me/theorems/39e27ded-91e5-4a7d-8adf-1a9a06115a49
-- title:
--   Weighted Global Prefix Seed Header: budget segment
-- statement:
--   The six previous scalar budgets are actual cells of the live header.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixSeedHeader.lean#L115-L123
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixSeedHeader.lean#L115-L123

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixSeedHeader
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPrefixSeedHeader
open Light LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
open LightWeightedGlobalPrefixStep LightWeightedGlobalPrefixHeader LightWeightedGlobalPrefixFinish
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalPrefixSeedHeader.budget_segment {C : Config} {μ : ℕ→ℤ} {seed n dB dC dP tB tC tP newSpan : ℕ}
    (H : Seg μ seed (header C n dB dC dP tB tC tP newSpan)) :
    Seg μ (seed+41) (LightTernaryBudgetStep.oldValues dB dC dP tB tC tP) := by sorry
