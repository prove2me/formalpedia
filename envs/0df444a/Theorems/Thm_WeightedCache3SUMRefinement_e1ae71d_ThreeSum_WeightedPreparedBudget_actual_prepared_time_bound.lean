-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedPreparedBudget_actual_prepared_time_bound
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPreparedBudget.actual_prepared_time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:02:56.291306+00:00
-- url     : https://prove2.me/theorems/955e66c7-bd9e-44b4-818f-8292702b75a9
-- title:
--   actual_prepared_time_bound
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/PreparedBudget.lean#L20-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/PreparedBudget.lean#L20-L73

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_QueryBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PreparedBudget
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPreparedBudget
open LightWeightedNearPair WeightedSchedule WeightedQueryBudget
open TernaryJointType
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPreparedBudget.actual_prepared_time_bound {m : ℕ} (f g : Config)
    (hT : f.T=bankCut m) (Q : TritWord (fixedLength m)) (hQ : HasType Q (fixedPi m)) :
    (LightWeightedPreparedWanted.time f g Q : ℝ)≤
      100000*(width (fixedLength m) f g : ℝ)^3*envelope m := by sorry
