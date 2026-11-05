-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedFrozenQuery_work_bank
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery.work_bank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:10:37.577104+00:00
-- url     : https://prove2.me/theorems/9456fd82-4202-4a40-a585-b6e3cf54f1a1
-- title:
--   work_bank
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/FrozenTime.lean#L21-L22
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/FrozenTime.lean#L21-L22

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenPrepare
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenQueryCost
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenTime
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryFrozenQueryStages
open ThreeSum.WeightedFrozenQueryCost
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery.work_bank {N : ℕ} (T : ℕ) (is : List (Fin N)) (R : TritWord N)
    (h : cacheCost R≤T) : work T is R=1 := by sorry
