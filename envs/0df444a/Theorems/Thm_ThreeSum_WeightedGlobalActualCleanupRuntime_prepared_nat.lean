-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualCleanupRuntime_prepared_nat
-- name    : ThreeSum.WeightedGlobalActualCleanupRuntime.prepared_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:25:50.832763+00:00
-- url     : https://prove2.me/theorems/870d727d-bfae-4615-94c4-c57361f71a77
-- title:
--   Weighted Global Actual Cleanup Runtime: prepared nat
-- statement:
--   Literal post-selection preparation, both exact collision cleanup passes,
--   and both compactions. The reporter's actual cost remains an explicit term.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualCleanupRuntime.lean#L37-L65
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualCleanupRuntime.lean#L37-L65

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_Submission_Weighted_Global_CountFrontendBudget
import Definitions.Def_Submission_Weighted_Global_TernaryActualCleanupRuntime
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalActualCleanupRuntime
open Light WeightedGlobalLocalParameters
set_option maxHeartbeats 6000000

theorem ThreeSum.WeightedGlobalActualCleanupRuntime.prepared_nat {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (H : ℕ)
    (c : LightOriginalSurvivorPair.Layout) (keysB keysC : ℕ→ℕ) (n : ℕ)
    (hA : c.nA≤n) (hB : c.nB≤n) (hC : c.nC≤n) :
    LightWeightedGlobalPreparedPostSelection.time S H c keysB keysC+673≤
      LightWeightedGlobalMomentReporter.time S H+
        10000*(c.L+1)*(n+c.q+1+(collisions keysB c.nB+collisions keysC c.nC)*(n+1)) := by sorry
