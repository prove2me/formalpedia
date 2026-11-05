-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedPreparedBudget_rank_time_bound
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPreparedBudget.rank_time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:02:41.193741+00:00
-- url     : https://prove2.me/theorems/def6e544-d604-4e7b-ab90-d04e50e288a5
-- title:
--   rank_time_bound
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/PreparedBudget.lean#L16-L18
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/PreparedBudget.lean#L16-L18

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPreparedBudget.rank_time_bound (N : ℕ) : LightWeightedCost.time N≤2000*(N+1)^2 := by sorry
