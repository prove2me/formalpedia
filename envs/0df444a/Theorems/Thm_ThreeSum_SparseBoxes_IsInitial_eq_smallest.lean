-- Prove2me | Theorems.Thm_ThreeSum_SparseBoxes_IsInitial_eq_smallest
-- name    : ThreeSum.SparseBoxes.IsInitial.eq_smallest
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:14:15.380662+00:00
-- url     : https://prove2.me/theorems/8592c59c-aac2-4ca5-b872-75adc6fd8992
-- title:
--   Is Initial: eq smallest
-- statement:
--   Thus a canonical free set is encoded solely by its cardinality.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L218-L221
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L218-L221

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.ByContra
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_SparseBoxes
set_option autoImplicit false
open ThreeSum ThreeSum.SparseBoxes
open scoped BigOperators
variable {α : Type*} [LinearOrder α]

theorem ThreeSum.SparseBoxes.IsInitial.eq_smallest {flags free : Finset α}
    (h : IsInitial flags free) : free = smallest free.card flags := by sorry
