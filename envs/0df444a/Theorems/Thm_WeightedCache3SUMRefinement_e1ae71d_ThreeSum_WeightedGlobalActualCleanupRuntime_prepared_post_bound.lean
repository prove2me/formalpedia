-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalActualCleanupRuntime_prepared_post_bound
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualCleanupRuntime.prepared_post_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T13:08:07.206193+00:00
-- url     : https://prove2.me/theorems/3d93160f-8c62-44f1-96d7-ee9827a9ef3e
-- title:
--   prepared_post_bound
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryActualCleanupRuntime.lean#L69-L120
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryActualCleanupRuntime.lean#L69-L120

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_CountFrontendBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualCleanupRuntime
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualCleanupRuntime
open Light WeightedGlobalLocalParameters
set_option maxHeartbeats 6000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualCleanupRuntime.prepared_post_bound {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (H : ℕ)
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
