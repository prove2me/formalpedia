-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalParameters_projection_fiber_log_choose_bound
-- name    : ThreeSum.WeightedGlobalParameters.projection_fiber_log_choose_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:56:10.190575+00:00
-- url     : https://prove2.me/theorems/71b08193-6e1c-4da0-8baa-fb17020fbf72
-- title:
--   Weighted Global Parameters: projection fiber log choose bound
-- statement:
--   Exact finite bound on the mixed projection fiber in the integer schedule.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L140-L161
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L140-L161

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ThreeSum.WeightedGlobalParameters.projection_fiber_log_choose_bound {m : ℕ} (hm : 0 < m) :
    Real.log (((30000000000000 * m).choose (292746547000 * m) : ℕ) : ℝ) <
      (30000000000000 * m : ℕ) * Real.log 2 / 4 := by sorry
