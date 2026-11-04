-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualCleanupRuntime_prepared_post_bound
-- name    : ThreeSum.WeightedGlobalActualCleanupRuntime.prepared_post_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:25:39.358274+00:00
-- url     : https://prove2.me/theorems/87011fd6-2168-44c0-9341-717ee4cbda26
-- title:
--   Weighted Global Actual Cleanup Runtime: prepared post bound
-- statement:
--   The real executed cleanup and preparation fit below the frontend
--   exponent, using both actual original collision-cardinality bounds.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualCleanupRuntime.lean#L69-L120
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualCleanupRuntime.lean#L69-L120

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_Submission_Weighted_Global_CountFrontendBudget
import Definitions.Def_Submission_Weighted_Global_TernaryActualCleanupRuntime
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalActualCleanupRuntime
open Light WeightedGlobalLocalParameters
set_option maxHeartbeats 6000000

theorem ThreeSum.WeightedGlobalActualCleanupRuntime.prepared_post_bound {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (H : ℕ)
    (c : LightOriginalSurvivorPair.Layout) (keysB keysC : ℕ→ℕ) (m J n : ℕ) (V : ℝ)
    (hn : 1<n) (hV : 0≤V)
    (hA : c.nA≤n) (hB : c.nB≤n) (hC : c.nC≤n)
    (hq : (c.q : ℝ)≤V*(n : ℝ)^WeightedGlobalCountFrontendBudget.frontendExponent)
    (hL : c.L≤2*fixedLength m*J)
    (hcolB : (collisions keysB c.nB : ℝ)≤(n : ℝ)^(7483/10000 : ℝ))
    (hcolC : (collisions keysC c.nC : ℝ)≤(n : ℝ)^(7483/10000 : ℝ)) :
    (LightWeightedGlobalPreparedPostSelection.time S H c keysB keysC+673 : ℕ)≤
      (LightWeightedGlobalMomentReporter.time S H : ℝ)+
        (1000000*(fixedLength m+1) : ℕ)*(J+1:ℕ)*(V+1)*
          (n : ℝ)^WeightedGlobalCountFrontendBudget.frontendExponent := by sorry
