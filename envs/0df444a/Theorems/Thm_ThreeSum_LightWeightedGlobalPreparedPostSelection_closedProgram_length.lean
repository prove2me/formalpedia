-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPreparedPostSelection_closedProgram_length
-- name    : ThreeSum.LightWeightedGlobalPreparedPostSelection.closedProgram_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:22:47.701979+00:00
-- url     : https://prove2.me/theorems/03e929fe-1889-4b73-b7d2-bcb664824785
-- title:
--   Light Weighted Global Prepared Post Selection: closed Program length
-- statement:
--   The Light Weighted Global Prepared Post Selection construction uses the closed Program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPreparedPostSelection.lean#L216-L228
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPreparedPostSelection.lean#L216-L228

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightTernaryFinalPreparation
import Definitions.Def_Submission_Weighted_Global_LightTernaryPostSelectionClosed
import Definitions.Def_Submission_Weighted_Global_LightTernaryPreparedPostSelection
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalPreparedPostSelection
open Light LightSubsetAddress LightOriginalSurvivorPair LightOriginalCollisionCleanup
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedGlobalPreparedPostSelection.closedProgram_length (xl yl zl xr yr zr : List ℤ) (H : ℕ) :
    (closedProgram xl yl zl xr yr zr H).length =
      139*(TernaryMomentSchedule.channels (2*H+1)).length+25 := by sorry
