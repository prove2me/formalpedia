-- Prove2me | Theorems.Thm_ThreeSum_TernaryPartialEuler_predecessor_kernel
-- name    : ThreeSum.TernaryPartialEuler.predecessor_kernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:21:24.767309+00:00
-- url     : https://prove2.me/theorems/3339db0b-7218-41cd-b38b-5b074924d9ee
-- title:
--   Ternary Partial Euler: predecessor kernel
-- statement:
--   The Ternary Partial Euler construction uses the predecessor kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartialEuler.lean#L22-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartialEuler.lean#L22-L32

import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPartialEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryTransform
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryPartialEuler.predecessor_kernel {N : ℕ} (S : Finset (Fin N)) (R A : TritWord N)
    (i : Fin N) (hi : i∈S) :
    kernel S (predecessor R i) A=digitChoose (predDigit (R i)) (A i)*
      ∏ j∈(univ : Finset (Fin N)).erase i,
        if j∈S then digitChoose (R j) (A j) else if A j=R j then 1 else 0 := by sorry
