-- Prove2me | Theorems.Thm_ThreeSum_TernaryJointType_joint_type_unique_rat
-- name    : ThreeSum.TernaryJointType.joint_type_unique_rat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:29:57.04569+00:00
-- url     : https://prove2.me/theorems/6144a53f-b288-4f80-a6fb-013b8ec1c315
-- title:
--   Ternary Joint Type: joint type unique rat
-- statement:
--   The same uniqueness identity over the rationals.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryJointType.lean#L126-L134
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryJointType.lean#L126-L134

import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryJointType
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryJointType
open Finset

theorem ThreeSum.TernaryJointType.joint_type_unique_rat
    (x00 x01 x02 x10 x11 x20 p0 p1 p2 a1 a2 : ℚ)
    (h00 : x00 = p0) (h02 : x02 = a2) (h20 : x20 = a2)
    (hrow1 : x10 + x11 = a1) (hcol1 : x01 + x11 = a1)
    (hout1 : x01 + x10 = p1) (hout2 : x02 + x11 + x20 = p2)
    (hthirds : p2 = 3 * a2) :
    x00 = p0 ∧ x01 = p1 / 2 ∧ x10 = p1 / 2 ∧
      x02 = p2 / 3 ∧ x11 = p2 / 3 ∧ x20 = p2 / 3 := by sorry
