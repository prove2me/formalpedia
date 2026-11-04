-- Prove2me | Theorems.Thm_ThreeSum_TernaryJointType_fieldWord_sum
-- name    : ThreeSum.TernaryJointType.fieldWord_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:30:17.625552+00:00
-- url     : https://prove2.me/theorems/a2b6043c-d486-4699-919f-1f6063a30120
-- title:
--   Ternary Joint Type: field Word sum
-- statement:
--   The Ternary Joint Type construction uses the field Word sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryJointType.lean#L187-L192
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryJointType.lean#L187-L192

import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryJointType
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryJointType
open Finset

theorem ThreeSum.TernaryJointType.fieldWord_sum {L p : ℕ} {a b q : TritWord L}
    (hsum : PointwiseSum a b q) :
    ∀ i, fieldWord p a i + fieldWord p b i = fieldWord p q i := by sorry
