-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPredecessor_code_lt
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessor.code_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:10:51.211149+00:00
-- url     : https://prove2.me/theorems/558f38bd-07f8-4351-bb14-be51cf09d3ba
-- title:
--   code_lt
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Predecessor.lean#L37-L43
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Predecessor.lean#L37-L43

import Definitions.Def_Submission_ThreeSum_LightTernaryRankTable
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightCost
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Predecessor
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low
import Theorems.Thm_ThreeSum_TernaryAddresses_code_lt
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedAddresses_code_lt

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessor
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryCodeSemantics
open ThreeSum.TernaryEuler
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessor.code_lt {N low high m : ℕ} (hm : m<2^(2*N)) :
    code N low high m<2^(2*N) := by sorry
