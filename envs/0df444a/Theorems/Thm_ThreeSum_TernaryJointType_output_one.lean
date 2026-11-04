-- Prove2me | Theorems.Thm_ThreeSum_TernaryJointType_output_one
-- name    : ThreeSum.TernaryJointType.output_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:28:56.1166+00:00
-- url     : https://prove2.me/theorems/8903996a-2ac6-42c8-adef-c725605a60b9
-- title:
--   Ternary Joint Type: output one
-- statement:
--   The Ternary Joint Type construction uses the output one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryJointType.lean#L95-L102
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryJointType.lean#L95-L102

import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryJointType
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryJointType
open Finset

theorem ThreeSum.TernaryJointType.output_one {L : ℕ} {a b q : TritWord L}
    (hsum : PointwiseSum a b q) :
    digitCount q 1 = jointCount a b 0 1 + jointCount a b 1 0 := by sorry
