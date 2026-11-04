-- Prove2me | Theorems.Thm_ThreeSum_WeightedNearCanonical_outside_complete
-- name    : ThreeSum.WeightedNearCanonical.outside_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:11:10.812905+00:00
-- url     : https://prove2.me/theorems/74f83276-c4cf-45f6-b1a0-8bb4f0b754a0
-- title:
--   Weighted Near Canonical: outside complete
-- statement:
--   Every outside-bank descendant required by Euler or inversion is emitted.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearCanonical.lean#L97-L101
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearCanonical.lean#L97-L101

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

theorem ThreeSum.WeightedNearCanonical.outside_complete {N T : ℕ} (Q R : TritWord N) (hQ : T<cacheCost Q)
    (hRQ : Below R Q) (hR : T<cacheCost R) :
    ∃ j<(WeightedNearEnumeration.codes (wordList Q) (cacheCost Q-(T+1))).length,
      word Q (cacheCost Q-(T+1)) j=R := by sorry
