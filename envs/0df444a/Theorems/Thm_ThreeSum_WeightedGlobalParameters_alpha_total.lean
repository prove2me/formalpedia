-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalParameters_alpha_total
-- name    : ThreeSum.WeightedGlobalParameters.alpha_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:56:10.90341+00:00
-- url     : https://prove2.me/theorems/c0100433-07d4-4c49-8162-30d29f5194a6
-- title:
--   Weighted Global Parameters: alpha total
-- statement:
--   The Weighted Global Parameters construction uses the alpha total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L100-L101
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L100-L101

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ThreeSum.WeightedGlobalParameters.alpha_total : alpha0 + alpha1 + alpha2 = 1 := by sorry
