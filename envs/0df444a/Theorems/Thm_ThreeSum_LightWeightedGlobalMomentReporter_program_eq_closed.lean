-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalMomentReporter_program_eq_closed
-- name    : ThreeSum.LightWeightedGlobalMomentReporter.program_eq_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:21:43.615232+00:00
-- url     : https://prove2.me/theorems/4bf23aea-fde8-4b99-b2a4-02aebc6c0157
-- title:
--   Light Weighted Global Moment Reporter: program eq closed
-- statement:
--   Compact source lengths, scalar/hash pointers, native dimensions and all
--   workspace parameters are runtime arguments. The program text is fixed by
--   the six literal local tables and the fixed physical support order.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryMomentReporter.lean#L50-L55
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryMomentReporter.lean#L50-L55

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryMomentDriverResources
import Definitions.Def_Submission_ThreeSum_LightTernaryPhysicalMomentBatch
import Definitions.Def_Submission_Weighted_Global_LightTernaryMomentReporter
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalMomentReporter
open Light TernaryMomentSchedule
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 100000

theorem ThreeSum.LightWeightedGlobalMomentReporter.program_eq_closed {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (H : ℕ) :
    program S H=closedProgram S.left.xs S.left.ys S.left.zs S.right.xs S.right.ys S.right.zs H := by sorry
