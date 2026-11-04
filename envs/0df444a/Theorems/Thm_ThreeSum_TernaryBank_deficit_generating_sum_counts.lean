-- Prove2me | Theorems.Thm_ThreeSum_TernaryBank_deficit_generating_sum_counts
-- name    : ThreeSum.TernaryBank.deficit_generating_sum_counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:33:46.71251+00:00
-- url     : https://prove2.me/theorems/86888c0f-3f69-4524-ba2c-47f5d5d937c6
-- title:
--   Ternary Bank: deficit generating sum counts
-- statement:
--   The Ternary Bank construction uses the deficit generating sum counts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L186-L189
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L186-L189

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

theorem ThreeSum.TernaryBank.deficit_generating_sum_counts {N : ℕ} (Q : TritWord N) (z : ℝ) :
    (∑ R ∈ lowerWords Q, z ^ deficit Q R) =
    (1 + z) ^ digitCount Q 1 * (1 + z + z ^ 2) ^ digitCount Q 2 := by sorry
