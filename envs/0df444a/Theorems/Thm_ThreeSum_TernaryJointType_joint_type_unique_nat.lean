-- Prove2me | Theorems.Thm_ThreeSum_TernaryJointType_joint_type_unique_nat
-- name    : ThreeSum.TernaryJointType.joint_type_unique_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:29:56.84202+00:00
-- url     : https://prove2.me/theorems/a8e4291f-1974-40e6-9c4d-af1c2907f8cd
-- title:
--   Ternary Joint Type: joint type unique nat
-- statement:
--   Pure marginal arithmetic; no joint type is selected or assumed.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryJointType.lean#L115-L123
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryJointType.lean#L115-L123

import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryJointType
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryJointType
open Finset

theorem ThreeSum.TernaryJointType.joint_type_unique_nat
    (x00 x01 x02 x10 x11 x20 p0 p1 p2 a1 a2 : ℕ)
    (h00 : x00 = p0) (h02 : x02 = a2) (h20 : x20 = a2)
    (hrow1 : x10 + x11 = a1) (hcol1 : x01 + x11 = a1)
    (hout1 : x01 + x10 = p1) (hout2 : x02 + x11 + x20 = p2)
    (hthirds : p2 = 3 * a2) :
    x00 = p0 ∧ x01 = p1 / 2 ∧ x10 = p1 / 2 ∧
      x02 = p2 / 3 ∧ x11 = p2 / 3 ∧ x20 = p2 / 3 := by sorry
