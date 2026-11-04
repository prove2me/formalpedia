-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPostSelection_program_eq_closed
-- name    : ThreeSum.LightWeightedGlobalPostSelection.program_eq_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:14:15.587848+00:00
-- url     : https://prove2.me/theorems/7c3ee294-140a-42b2-ad1d-57086a8da53f
-- title:
--   Light Weighted Global Post Selection: program eq closed
-- statement:
--   The Light Weighted Global Post Selection construction uses the program eq closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPostSelectionClosed.lean#L37-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPostSelectionClosed.lean#L37-L40

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPostSelection
import Definitions.Def_Submission_Weighted_Global_LightTernaryPostSelectionClosed
import Theorems.Thm_ThreeSum_LightWeightedGlobalMomentReporter_program_eq_closed

set_option autoImplicit false
noncomputable section
set_option maxRecDepth 24000
set_option maxHeartbeats 1000000
open ThreeSum ThreeSum.LightWeightedGlobalPostSelection
open Light TernaryMomentSchedule

theorem ThreeSum.LightWeightedGlobalPostSelection.program_eq_closed {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (H : ℕ) :
    program S H = closedProgram S.left.xs S.left.ys S.left.zs S.right.xs S.right.ys S.right.zs H := by sorry
