-- Prove2me | Theorems.Thm_ThreeSum_TernaryPartialEuler_outside_difference_zero
-- name    : ThreeSum.TernaryPartialEuler.outside_difference_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:21:27.455981+00:00
-- url     : https://prove2.me/theorems/0bb0a458-2a27-4ba0-8bbf-a80a5172952c
-- title:
--   Ternary Partial Euler: outside difference zero
-- statement:
--   The Ternary Partial Euler construction uses the outside difference zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartialEuler.lean#L41-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartialEuler.lean#L41-L49

import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPartialEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryTransform
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryPartialEuler.outside_difference_zero {N : ℕ} (S : Finset (Fin N)) (R A : TritWord N)
    (i : Fin N) (hi : i∉S) :
    ((R i).val-(A i).val : ℤ)*kernel S R A=0 := by sorry
