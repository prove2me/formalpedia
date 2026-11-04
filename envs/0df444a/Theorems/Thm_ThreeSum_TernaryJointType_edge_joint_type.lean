-- Prove2me | Theorems.Thm_ThreeSum_TernaryJointType_edge_joint_type
-- name    : ThreeSum.TernaryJointType.edge_joint_type
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:29:57.920538+00:00
-- url     : https://prove2.me/theorems/df431b08-1182-418c-851c-bc80a4732b3a
-- title:
--   Ternary Joint Type: edge joint type
-- statement:
--   The six joint cells are forced for every actual edge of these types.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryJointType.lean#L137-L167
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryJointType.lean#L137-L167

import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryJointType
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryJointType
open Finset

theorem ThreeSum.TernaryJointType.edge_joint_type {L : ℕ} {α π : DigitType} {a b q : TritWord L}
    (hedge : Edge α π a b q) (hthirds : π 2 = 3 * α 2) :
    jointCount a b 0 0 = π 0 ∧
      jointCount a b 0 1 = π 1 / 2 ∧
      jointCount a b 1 0 = π 1 / 2 ∧
      jointCount a b 0 2 = π 2 / 3 ∧
      jointCount a b 1 1 = π 2 / 3 ∧
      jointCount a b 2 0 = π 2 / 3 := by sorry
