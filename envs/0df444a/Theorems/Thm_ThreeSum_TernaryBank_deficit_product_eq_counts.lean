-- Prove2me | Theorems.Thm_ThreeSum_TernaryBank_deficit_product_eq_counts
-- name    : ThreeSum.TernaryBank.deficit_product_eq_counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:33:48.71065+00:00
-- url     : https://prove2.me/theorems/368971f2-9600-4d82-b50e-6dc26c1df58e
-- title:
--   Ternary Bank: deficit product eq counts
-- statement:
--   The Ternary Bank construction uses the deficit product eq counts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L172-L184
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L172-L184

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

theorem ThreeSum.TernaryBank.deficit_product_eq_counts {N : ℕ} (Q : TritWord N) (z : ℝ) :
    (∏ i : Fin N, (if Q i = 0 then 1 else if Q i = 1 then 1 + z
      else 1 + z + z ^ 2)) =
    (1 + z) ^ digitCount Q 1 * (1 + z + z ^ 2) ^ digitCount Q 2 := by sorry
