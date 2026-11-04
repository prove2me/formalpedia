-- Prove2me | Theorems.Thm_ThreeSum_WeightedPhysicalEuler_numerator
-- name    : ThreeSum.WeightedPhysicalEuler.numerator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:23:43.755111+00:00
-- url     : https://prove2.me/theorems/affab590-e49b-42a4-9b10-0fbdaf409dcc
-- title:
--   Weighted Physical Euler: numerator
-- statement:
--   The physical signed numerator is the homogeneous Euler numerator, including
--   zero coordinates whose actual reads use the safe dummy bank cell.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PhysicalEuler.lean#L115-L137
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PhysicalEuler.lean#L115-L137

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

theorem ThreeSum.WeightedPhysicalEuler.numerator {N nb nn T bv nv h : ℕ} (R : TritWord N)
    (bankWords nearWords : ℕ → TritWord N) (f : TritWord N → ℤ)
    (hf : ∀ A, f A≠0 → rank A=h) (hcut : h≤rank R)
    (hsep : bv+nb≤nv)
    (hbank : ∀ W, cacheCost W≤T → ∃ j<nb, bankWords j=W)
    (hnear : ∀ i : Fin N, T<cacheCost (predecessor R i) → ∃ j<nn, nearWords j=predecessor R i) :
    LightTernaryWeightedSum.sum (rowWeight R) (rowKey R bankWords nearWords nb nn T bv nv)
      (physicalValue (binomialZeta f) bankWords nearWords bv nv) N=
      (rank R-h : ℕ)*binomialZeta f R := by sorry
