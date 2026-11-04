-- Prove2me | Theorems.Thm_ThreeSum_TernaryJointType_jointCount_row
-- name    : ThreeSum.TernaryJointType.jointCount_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:28:44.966225+00:00
-- url     : https://prove2.me/theorems/469567ac-5005-457c-9083-9be5234bf965
-- title:
--   Ternary Joint Type: joint Count row
-- statement:
--   The Ternary Joint Type construction uses the joint Count row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryJointType.lean#L37-L43
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryJointType.lean#L37-L43

import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryJointType
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryJointType
open Finset

theorem ThreeSum.TernaryJointType.jointCount_row {L : ℕ} (a b : TritWord L) (u : Fin 3) :
    ∑ v : Fin 3, jointCount a b u v = digitCount a u := by sorry
