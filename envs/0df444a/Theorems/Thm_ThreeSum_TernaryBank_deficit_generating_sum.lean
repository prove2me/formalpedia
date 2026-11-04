-- Prove2me | Theorems.Thm_ThreeSum_TernaryBank_deficit_generating_sum
-- name    : ThreeSum.TernaryBank.deficit_generating_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:33:42.181208+00:00
-- url     : https://prove2.me/theorems/f6a7dcd3-4b91-4405-b2a8-13820b5a09a9
-- title:
--   Ternary Bank: deficit generating sum
-- statement:
--   The Ternary Bank construction uses the deficit generating sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L140-L170
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L140-L170

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

theorem ThreeSum.TernaryBank.deficit_generating_sum {N : ℕ} (Q : TritWord N) (z : ℝ) :
    (∑ R ∈ lowerWords Q, z ^ deficit Q R) =
      ∏ i : Fin N, (if Q i = 0 then 1 else if Q i = 1 then 1 + z
        else 1 + z + z ^ 2) := by sorry
