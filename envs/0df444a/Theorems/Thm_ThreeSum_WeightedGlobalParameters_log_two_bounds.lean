-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalParameters_log_two_bounds
-- name    : ThreeSum.WeightedGlobalParameters.log_two_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:02:55.815693+00:00
-- url     : https://prove2.me/theorems/a0e12065-15f2-46eb-886f-1e623770af7c
-- title:
--   Weighted Global Parameters: log two bounds
-- statement:
--   The Weighted Global Parameters construction uses the log two bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L34-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L34-L42

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ThreeSum.WeightedGlobalParameters.log_two_bounds :
    (693147180559945309/1000000000000000000 : ℝ)≤Real.log 2 ∧
    Real.log 2≤(69314718055994531/100000000000000000 : ℝ) := by sorry
