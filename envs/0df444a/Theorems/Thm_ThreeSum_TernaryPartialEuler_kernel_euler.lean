-- Prove2me | Theorems.Thm_ThreeSum_TernaryPartialEuler_kernel_euler
-- name    : ThreeSum.TernaryPartialEuler.kernel_euler
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:21:28.056203+00:00
-- url     : https://prove2.me/theorems/17b02f96-c0d7-480d-9e16-4f41d55a0fee
-- title:
--   Ternary Partial Euler: kernel euler
-- statement:
--   The Ternary Partial Euler construction uses the kernel euler property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartialEuler.lean#L51-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartialEuler.lean#L51-L66

import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPartialEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryTransform
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryPartialEuler.kernel_euler {N : ℕ} (S : Finset (Fin N)) (R A : TritWord N) :
    (∑ i∈S, (R i).val*kernel S (predecessor R i) A)=
      ((rank R : ℤ)-(rank A : ℤ))*kernel S R A := by sorry
