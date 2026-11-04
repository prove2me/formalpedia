-- Prove2me | Theorems.Thm_ThreeSum_TernaryEuler_coordinate_weight_euler
-- name    : ThreeSum.TernaryEuler.coordinate_weight_euler
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:37:48.462864+00:00
-- url     : https://prove2.me/theorems/5c7930b6-1955-40c2-a516-25f39dceb390
-- title:
--   Ternary Euler: coordinate weight euler
-- statement:
--   The Ternary Euler construction uses the coordinate weight euler property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEuler.lean#L49-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEuler.lean#L49-L53

import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Definitions.Def_Submission_ThreeSum_TernaryEuler
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryEuler
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank

theorem ThreeSum.TernaryEuler.coordinate_weight_euler {N : ℕ} (R A : TritWord N) (i : Fin N) :
    (R i).val * weight (predecessor R i) A =
      ((R i).val - (A i).val : ℤ) * weight R A := by sorry
