-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalEuler_numerator
-- name    : ThreeSum.TernaryPhysicalEuler.numerator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:30:09.850096+00:00
-- url     : https://prove2.me/theorems/f4395fc6-a33c-48ed-b78f-c0b776ab76f8
-- title:
--   Ternary Physical Euler: numerator
-- statement:
--   The physical signed numerator is the homogeneous Euler numerator, including
--   zero coordinates whose actual reads use the safe dummy bank cell.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalEuler.lean#L109-L131
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalEuler.lean#L109-L131

import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalEuler
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPhysicalEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 3000000

theorem ThreeSum.TernaryPhysicalEuler.numerator {N nb nn T bv nv h : ℕ} (R : TritWord N)
    (bankWords nearWords : ℕ → TritWord N) (f : TritWord N → ℤ)
    (hf : ∀ A, f A≠0 → rank A=h) (hcut : h≤rank R)
    (hsep : bv+nb≤nv)
    (hbank : ∀ W, rank W≤T → ∃ j<nb, bankWords j=W)
    (hnear : ∀ i : Fin N, T<rank (predecessor R i) → ∃ j<nn, nearWords j=predecessor R i) :
    LightTernaryWeightedSum.sum (rowWeight R) (rowKey R bankWords nearWords nb nn T bv nv)
      (physicalValue (binomialZeta f) bankWords nearWords bv nv) N=
      (rank R-h : ℕ)*binomialZeta f R := by sorry
