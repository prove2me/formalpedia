-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPredecessor_predCost_canonical
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessor.predCost_canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:09:52.969842+00:00
-- url     : https://prove2.me/theorems/eec36d7b-948f-453e-a71b-5353d7b59003
-- title:
--   predCost_canonical
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Predecessor.lean#L240-L244
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Predecessor.lean#L240-L244

import Definitions.Def_Submission_ThreeSum_LightTernaryRankTable
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightCost
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Predecessor
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessor
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryCodeSemantics
open ThreeSum.TernaryEuler
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessor.predCost_canonical {N : ℕ} (R : TritWord N) (i : Fin N)
    (hi : 0<(R i).val) :
    predCost N (low i) (high i) (address R)=WeightedBankEnumeration.cacheCost (predecessor R i) := by sorry
