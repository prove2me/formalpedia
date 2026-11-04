-- Prove2me | Theorems.Thm_ThreeSum_SparseBoxes_boxSum_resolve
-- name    : ThreeSum.SparseBoxes.boxSum_resolve
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:01:41.732258+00:00
-- url     : https://prove2.me/theorems/9c6187f8-57e6-4b22-a28b-480c44e8aae5
-- title:
--   Sparse Boxes: box Sum resolve
-- statement:
--   Resolving one free flag is exactly one addition of an included child and an
--   excluded child. The theorem applies to arbitrary signed leaf values.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L402-L462
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L402-L462

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

theorem ThreeSum.SparseBoxes.boxSum_resolve (flags free : Finset α) (weight : Finset α → ℤ)
    (a : α) (hfree : free ⊆ flags) (ha : a ∈ free) :
    boxSum flags free weight =
      boxSum flags (free.erase a) weight +
      boxSum (flags.erase a) (free.erase a) weight := by sorry
