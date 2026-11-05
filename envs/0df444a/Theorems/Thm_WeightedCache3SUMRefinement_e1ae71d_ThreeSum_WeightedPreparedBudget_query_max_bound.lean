-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedPreparedBudget_query_max_bound
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPreparedBudget.query_max_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:03:00.477223+00:00
-- url     : https://prove2.me/theorems/6f617e20-3644-4bd4-8aa7-44316d9b1934
-- title:
--   query_max_bound
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/PreparedBudget.lean#L89-L105
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/PreparedBudget.lean#L89-L105

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPreparedBudget.query_max_bound {m : ℕ} (f g : Config) (hT : f.T=bankCut m) :
    (queryMax m f g : ℝ)≤100000*(width (fixedLength m) f g : ℝ)^3*envelope m := by sorry
