-- Prove2me | Theorems.Thm_ThreeSum_TernaryPartialEuler_kernel_split
-- name    : ThreeSum.TernaryPartialEuler.kernel_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:21:24.635207+00:00
-- url     : https://prove2.me/theorems/3c9c0056-5f7a-4ddb-b56f-b3477112eb98
-- title:
--   Ternary Partial Euler: kernel split
-- statement:
--   The Ternary Partial Euler construction uses the kernel split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartialEuler.lean#L13-L20
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartialEuler.lean#L13-L20

import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPartialEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryTransform
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryPartialEuler.kernel_split {N : ℕ} (S : Finset (Fin N)) (R A : TritWord N)
    (i : Fin N) (hi : i∈S) :
    kernel S R A=digitChoose (R i) (A i)*
      ∏ j∈(univ : Finset (Fin N)).erase i,
        if j∈S then digitChoose (R j) (A j) else if A j=R j then 1 else 0 := by sorry
