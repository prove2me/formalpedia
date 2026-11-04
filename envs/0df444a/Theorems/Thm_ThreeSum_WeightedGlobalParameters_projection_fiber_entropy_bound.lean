-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalParameters_projection_fiber_entropy_bound
-- name    : ThreeSum.WeightedGlobalParameters.projection_fiber_entropy_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:17:41.809955+00:00
-- url     : https://prove2.me/theorems/652619d8-263a-4166-92c5-c6f82956ef5d
-- title:
--   Weighted Global Parameters: projection fiber entropy bound
-- statement:
--   The exceptional mixed-projection binomial fiber has a strict quarter-bit margin.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L121-L132
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L121-L132

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ThreeSum.WeightedGlobalParameters.projection_fiber_entropy_bound :
    Real.binEntropy alpha2 / Real.log 2 < (1 / 4 : ℝ) := by sorry
