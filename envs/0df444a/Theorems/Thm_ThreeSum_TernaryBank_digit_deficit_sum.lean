-- Prove2me | Theorems.Thm_ThreeSum_TernaryBank_digit_deficit_sum
-- name    : ThreeSum.TernaryBank.digit_deficit_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:33:43.975488+00:00
-- url     : https://prove2.me/theorems/0d27632a-c22e-4946-8833-3591cfb03380
-- title:
--   Ternary Bank: digit deficit sum
-- statement:
--   The Ternary Bank construction uses the digit deficit sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L135-L138
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L135-L138

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryBank
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryBank
open Finset
open ThreeSum.TernaryJointType

theorem ThreeSum.TernaryBank.digit_deficit_sum (z : ℝ) (q : Fin 3) :
    (∑ r : Fin 3, digitDeficitWeight z q r) =
      if q = 0 then 1 else if q = 1 then 1 + z else 1 + z + z ^ 2 := by sorry
