-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCost_partialCost_le
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCost.partialCost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:08:49.208274+00:00
-- url     : https://prove2.me/theorems/a1bec899-9767-4be8-aa7c-115f3958eaa8
-- title:
--   partialCost_le
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/LightCost.lean#L27-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/LightCost.lean#L27-L37

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightCost
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCost
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
open ThreeSum.WeightedEnumeration
open Light Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.LightSubsetAddress

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCost.partialCost_le (N m j : ℕ) : partialCost N m j ≤ 2740*j := by sorry
