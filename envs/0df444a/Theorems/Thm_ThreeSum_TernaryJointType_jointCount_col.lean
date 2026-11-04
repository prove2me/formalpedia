-- Prove2me | Theorems.Thm_ThreeSum_TernaryJointType_jointCount_col
-- name    : ThreeSum.TernaryJointType.jointCount_col
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:28:48.542904+00:00
-- url     : https://prove2.me/theorems/5fbf7af6-b878-4a27-959e-74d3b1c30b39
-- title:
--   Ternary Joint Type: joint Count col
-- statement:
--   The Ternary Joint Type construction uses the joint Count col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryJointType.lean#L45-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryJointType.lean#L45-L51

import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryJointType
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryJointType
open Finset

theorem ThreeSum.TernaryJointType.jointCount_col {L : ℕ} (a b : TritWord L) (v : Fin 3) :
    ∑ u : Fin 3, jointCount a b u v = digitCount b v := by sorry
