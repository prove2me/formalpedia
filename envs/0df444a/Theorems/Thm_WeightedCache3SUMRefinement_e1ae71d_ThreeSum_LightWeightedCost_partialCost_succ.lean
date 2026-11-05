-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCost_partialCost_succ
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCost.partialCost_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:08:53.587801+00:00
-- url     : https://prove2.me/theorems/4c1dc0e9-d0a9-47c6-9e1e-fa97a827ba64
-- title:
--   partialCost_succ
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/LightCost.lean#L24-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/LightCost.lean#L24-L25

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCost.partialCost_succ (N m j : ℕ) :
    partialCost N m (j+1)=partialCost N m j+digitCost (digitAt N m j) := by sorry
