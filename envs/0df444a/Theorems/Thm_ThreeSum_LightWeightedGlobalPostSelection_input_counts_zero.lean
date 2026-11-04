-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPostSelection_input_counts_zero
-- name    : ThreeSum.LightWeightedGlobalPostSelection.input_counts_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:15:36.961794+00:00
-- url     : https://prove2.me/theorems/3c5a9192-9a43-4a68-bb00-37bc13c296d3
-- title:
--   Light Weighted Global Post Selection: input counts zero
-- statement:
--   Every compact count in the input frame is a literal zero; the program
--   loads its actual values only after the original-source cleanup has run.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPostSelectionClosed.lean#L57-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPostSelectionClosed.lean#L57-L63

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPostSelection
import Definitions.Def_Submission_Weighted_Global_LightTernaryPostSelectionClosed
set_option autoImplicit false
noncomputable section
set_option maxRecDepth 24000
set_option maxHeartbeats 1000000
open ThreeSum ThreeSum.LightWeightedGlobalPostSelection
open Light TernaryMomentSchedule

theorem ThreeSum.LightWeightedGlobalPostSelection.input_counts_zero {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (c : LightOriginalSurvivorPair.Layout) (scratch matrix : ℕ) :
    (args S c scratch matrix).getD 34 0 = 0 ∧
    (args S c scratch matrix).getD 36 0 = 0 ∧
    (args S c scratch matrix).getD 53 0 = 0 ∧
    (args S c scratch matrix).getD 76 0 = 0 := by sorry
