-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearCanonical_outside_near_iff
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearCanonical.outside_near_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:44:53.345638+00:00
-- url     : https://prove2.me/theorems/1cb10c92-fde9-4596-9087-323bfb7d2719
-- title:
--   outside_near_iff
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/NearCanonical.lean#L76-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/NearCanonical.lean#L76-L87

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearPair
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearCanonical
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearCanonical
open ThreeSum.TernaryJointType ThreeSum.WeightedNearBankEnumeration ThreeSum.WeightedBankEnumeration
open ThreeSum.TernaryBank (Below)
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearCanonical.outside_near_iff {N : ℕ} (Q R : TritWord N) (T : ℕ) (hQ : T<cacheCost Q) :
    R∈nearWords Q (cacheCost Q-(T+1)) ↔ Below R Q ∧ T<cacheCost R := by sorry
