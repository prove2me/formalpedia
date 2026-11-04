-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPreparedPostSelection_program_eq_closed
-- name    : ThreeSum.LightWeightedGlobalPreparedPostSelection.program_eq_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:46:50.668209+00:00
-- url     : https://prove2.me/theorems/f93583b5-99fc-46d4-bb85-1e08e468087e
-- title:
--   Light Weighted Global Prepared Post Selection: program eq closed
-- statement:
--   The Light Weighted Global Prepared Post Selection construction uses the program eq closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPreparedPostSelection.lean#L200-L203
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPreparedPostSelection.lean#L200-L203

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightTernaryFinalPreparation
import Definitions.Def_Submission_Weighted_Global_LightTernaryPostSelectionClosed
import Definitions.Def_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Theorems.Thm_ThreeSum_LightWeightedGlobalCompactReporter_program_eq_closed
import Theorems.Thm_ThreeSum_LightWeightedGlobalMomentReporter_program_eq_closed
import Theorems.Thm_ThreeSum_LightWeightedGlobalPostSelection_program_eq_closed

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalPreparedPostSelection
open Light LightSubsetAddress LightOriginalSurvivorPair LightOriginalCollisionCleanup
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedGlobalPreparedPostSelection.program_eq_closed {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (H : ℕ) :
    program S H = closedProgram S.left.xs S.left.ys S.left.zs S.right.xs S.right.ys S.right.zs H := by sorry
