-- Prove2me | Theorems.Thm_ThreeSum_TernaryEuler_digit_euler
-- name    : ThreeSum.TernaryEuler.digit_euler
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:37:55.225294+00:00
-- url     : https://prove2.me/theorems/9d080128-4f82-4f8e-8c1d-5cb58405abb5
-- title:
--   Ternary Euler: digit euler
-- statement:
--   The Ternary Euler construction uses the digit euler property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEuler.lean#L29-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEuler.lean#L29-L32

import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Definitions.Def_Submission_ThreeSum_TernaryEuler
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryEuler
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank

theorem ThreeSum.TernaryEuler.digit_euler (r a : Fin 3) :
    (r.val : ℤ) * digitChoose (predDigit r) a =
      ((r.val : ℤ) - (a.val : ℤ)) * digitChoose r a := by sorry
