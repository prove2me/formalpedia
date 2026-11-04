-- Prove2me | Theorems.Thm_ThreeSum_TernaryJointType_fieldWord_injective
-- name    : ThreeSum.TernaryJointType.fieldWord_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:30:16.767829+00:00
-- url     : https://prove2.me/theorems/7f260f30-2e2c-4f4c-b19e-e8c6c37ab21c
-- title:
--   Ternary Joint Type: field Word injective
-- statement:
--   The Ternary Joint Type construction uses the field Word injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryJointType.lean#L181-L185
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryJointType.lean#L181-L185

import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryJointType
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryJointType
open Finset

theorem ThreeSum.TernaryJointType.fieldWord_injective {L p : ℕ} (hp : 2 < p) :
    Function.Injective (fieldWord (L := L) p) := by sorry
