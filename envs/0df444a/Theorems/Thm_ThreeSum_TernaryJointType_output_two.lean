-- Prove2me | Theorems.Thm_ThreeSum_TernaryJointType_output_two
-- name    : ThreeSum.TernaryJointType.output_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:29:42.461235+00:00
-- url     : https://prove2.me/theorems/55f29510-f15d-4cee-b64b-a85022473c5e
-- title:
--   Ternary Joint Type: output two
-- statement:
--   The Ternary Joint Type construction uses the output two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryJointType.lean#L104-L112
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryJointType.lean#L104-L112

import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryJointType
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryJointType
open Finset

theorem ThreeSum.TernaryJointType.output_two {L : ℕ} {a b q : TritWord L}
    (hsum : PointwiseSum a b q) :
    digitCount q 2 = jointCount a b 0 2 + jointCount a b 1 1 +
      jointCount a b 2 0 := by sorry
