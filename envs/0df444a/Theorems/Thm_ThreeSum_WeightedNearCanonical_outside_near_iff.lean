-- Prove2me | Theorems.Thm_ThreeSum_WeightedNearCanonical_outside_near_iff
-- name    : ThreeSum.WeightedNearCanonical.outside_near_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:11:24.859505+00:00
-- url     : https://prove2.me/theorems/0d9e7ef7-b73e-48f5-b0f0-c431976af7d1
-- title:
--   Weighted Near Canonical: outside near iff
-- statement:
--   The Weighted Near Canonical construction uses the outside near iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearCanonical.lean#L76-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearCanonical.lean#L76-L87

import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_Weighted_NearPair
import Definitions.Def_Submission_Weighted_NearCanonical
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearCanonical
open ThreeSum.TernaryJointType ThreeSum.WeightedNearBankEnumeration ThreeSum.WeightedBankEnumeration
open ThreeSum.TernaryBank (Below)
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedNearCanonical.outside_near_iff {N : ℕ} (Q R : TritWord N) (T : ℕ) (hQ : T<cacheCost Q) :
    R∈nearWords Q (cacheCost Q-(T+1)) ↔ Below R Q ∧ T<cacheCost R := by sorry
