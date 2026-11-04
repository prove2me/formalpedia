-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalParameters_projection_fiber_entropy_lt_half_Hpi
-- name    : ThreeSum.WeightedGlobalParameters.projection_fiber_entropy_lt_half_Hpi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:57:26.641254+00:00
-- url     : https://prove2.me/theorems/9479d38c-7826-4e2e-b28b-6a783f41ca23
-- title:
--   Weighted Global Parameters: projection fiber entropy lt half Hpi
-- statement:
--   A `choose(L, alpha2*L)` fiber is strictly smaller than a half-Hpi layer.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L135-L137
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L135-L137

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ThreeSum.WeightedGlobalParameters.projection_fiber_entropy_lt_half_Hpi :
    Real.binEntropy alpha2 / Real.log 2 < Hpi / 2 := by sorry
