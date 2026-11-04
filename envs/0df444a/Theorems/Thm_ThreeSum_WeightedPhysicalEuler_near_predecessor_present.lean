-- Prove2me | Theorems.Thm_ThreeSum_WeightedPhysicalEuler_near_predecessor_present
-- name    : ThreeSum.WeightedPhysicalEuler.near_predecessor_present
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:58:16.501954+00:00
-- url     : https://prove2.me/theorems/80ebf86b-d748-4fb2-8036-66c9785cb80a
-- title:
--   Weighted Physical Euler: near predecessor present
-- statement:
--   A predecessor reached outside the bank is present in the same near segment.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PhysicalEuler.lean#L140-L145
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PhysicalEuler.lean#L140-L145

import Definitions.Def_Submission_Weighted_EulerMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Definitions.Def_Submission_Weighted_PhysicalEuler
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedPhysicalEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics
open ThreeSum.WeightedBankEnumeration (cacheCost)
set_option maxHeartbeats 3000000

theorem ThreeSum.WeightedPhysicalEuler.near_predecessor_present {N nn T : ℕ} (Q R : TritWord N)
    (nearWords : ℕ → TritWord N)
    (hnear : ∀ W, Below W Q → T<cacheCost W → ∃ j<nn, nearWords j=W)
    (hRQ : Below R Q) (i : Fin N) (hr : T<cacheCost (predecessor R i)) :
    ∃ j<nn, nearWords j=predecessor R i := by sorry
