-- Prove2me | Theorems.Thm_ThreeSum_TernaryJointType_jointCount_forbidden
-- name    : ThreeSum.TernaryJointType.jointCount_forbidden
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:28:50.342504+00:00
-- url     : https://prove2.me/theorems/992c97b4-32cb-4d7e-9efa-8d9ed9c50b02
-- title:
--   Ternary Joint Type: joint Count forbidden
-- statement:
--   The Ternary Joint Type construction uses the joint Count forbidden property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryJointType.lean#L53-L65
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryJointType.lean#L53-L65

import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryJointType
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryJointType
open Finset

theorem ThreeSum.TernaryJointType.jointCount_forbidden {L : ℕ} {a b q : TritWord L}
    (hsum : PointwiseSum a b q) (u v : Fin 3) (hlarge : 2 < u.val + v.val) :
    jointCount a b u v = 0 := by sorry
