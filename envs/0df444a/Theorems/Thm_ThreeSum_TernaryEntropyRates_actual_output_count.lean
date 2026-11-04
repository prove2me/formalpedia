-- Prove2me | Theorems.Thm_ThreeSum_TernaryEntropyRates_actual_output_count
-- name    : ThreeSum.TernaryEntropyRates.actual_output_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:52:06.806599+00:00
-- url     : https://prove2.me/theorems/d441702f-4b3d-4ba1-bad0-195c6dacde1c
-- title:
--   Ternary Entropy Rates: actual output count
-- statement:
--   The Ternary Entropy Rates construction uses the actual output count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEntropyRates.lean#L89-L95
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEntropyRates.lean#L89-L95

import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Definitions.Def_Submission_ThreeSum_TernaryEntropyRates
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryEntropyRates
open Filter Real
open scoped Topology
open TernaryJointType TernaryCoverLocal TernaryLocalParameters TernaryCoverScale
set_option maxRecDepth 10000

theorem ThreeSum.TernaryEntropyRates.actual_output_count (m : ℕ) :
    outputSize m=typeCount 100000000 15860450 2934804 m := by sorry
