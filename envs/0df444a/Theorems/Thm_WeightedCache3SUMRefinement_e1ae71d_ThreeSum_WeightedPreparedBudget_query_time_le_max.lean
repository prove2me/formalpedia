-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedPreparedBudget_query_time_le_max
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPreparedBudget.query_time_le_max
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:02:39.785049+00:00
-- url     : https://prove2.me/theorems/e55e86ba-2e05-4393-815f-14877f56f80b
-- title:
--   query_time_le_max
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/PreparedBudget.lean#L83-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/PreparedBudget.lean#L83-L87

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPreparedBudget.query_time_le_max {m : ℕ} (f g : Config) (Q : TritWord (fixedLength m))
    (hQ : HasType Q (fixedPi m)) :
    LightWeightedPreparedWanted.time f g Q≤queryMax m f g := by sorry
