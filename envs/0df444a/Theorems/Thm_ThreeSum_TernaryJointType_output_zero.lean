-- Prove2me | Theorems.Thm_ThreeSum_TernaryJointType_output_zero
-- name    : ThreeSum.TernaryJointType.output_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:28:57.908862+00:00
-- url     : https://prove2.me/theorems/75bd7978-7e9f-4607-8b73-d78b6e9bd633
-- title:
--   Ternary Joint Type: output zero
-- statement:
--   The Ternary Joint Type construction uses the output zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryJointType.lean#L87-L93
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryJointType.lean#L87-L93

import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryJointType
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryJointType
open Finset

theorem ThreeSum.TernaryJointType.output_zero {L : ℕ} {a b q : TritWord L}
    (hsum : PointwiseSum a b q) :
    digitCount q 0 = jointCount a b 0 0 := by sorry
