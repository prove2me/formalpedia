-- Prove2me | Theorems.Thm_ThreeSum_BandPrimeCosts_timeBudget_powerBound_w3sum_ac885d1
-- name    : ThreeSum.BandPrimeCosts.timeBudget_powerBound_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:36:04.812701+00:00
-- url     : https://prove2.me/theorems/cf77e9ea-140a-4287-8902-e77da164ec61
-- title:
--   Band Prime Costs: time Budget power Bound
-- statement:
--   Exact exponent of the size-only bound for all executed arithmetic work.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeCostBounds.lean#L55-L69
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeCostBounds.lean#L55-L69

import Definitions.Def_Submission_ThreeSum_BandPrimeCosts
import Definitions.Def_Submission_ThreeSum_BandPrimeCostBounds
set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeCosts
open Filter Real Scales BandScales CostLedger Parameters StageBounds HierarchyScales
  ArithmeticStageBounds
open scoped Topology
set_option maxHeartbeats 1400000
noncomputable section

theorem ThreeSum.BandPrimeCosts.timeBudget_powerBound_w3sum_ac885d1 (k : ℕ) :
    PowerBound (timeBudget k) (2+epsilon*(4/5-(2/5)*E-2*bandShift)) := by sorry
