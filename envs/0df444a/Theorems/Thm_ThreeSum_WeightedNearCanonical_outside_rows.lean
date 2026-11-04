-- Prove2me | Theorems.Thm_ThreeSum_WeightedNearCanonical_outside_rows
-- name    : ThreeSum.WeightedNearCanonical.outside_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:12:56.838202+00:00
-- url     : https://prove2.me/theorems/4f472a08-9558-4b99-9e4b-4eda17c398af
-- title:
--   Weighted Near Canonical: outside rows
-- statement:
--   With the exact cutoff, every emitted row lies outside the stored bank.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearCanonical.lean#L90-L94
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearCanonical.lean#L90-L94

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

theorem ThreeSum.WeightedNearCanonical.outside_rows {N j T : ℕ} (Q : TritWord N) (hQ : T<cacheCost Q)
    (hj : j<(WeightedNearEnumeration.codes (wordList Q) (cacheCost Q-(T+1))).length) :
    Below (word Q (cacheCost Q-(T+1)) j) Q ∧ T<cacheCost (word Q (cacheCost Q-(T+1)) j) := by sorry
