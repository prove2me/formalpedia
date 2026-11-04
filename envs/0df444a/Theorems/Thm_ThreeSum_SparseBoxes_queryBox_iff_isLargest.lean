-- Prove2me | Theorems.Thm_ThreeSum_SparseBoxes_queryBox_iff_isLargest
-- name    : ThreeSum.SparseBoxes.queryBox_iff_isLargest
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:14:09.031912+00:00
-- url     : https://prove2.me/theorems/003e7be9-8805-4764-a564-1226744cff2a
-- title:
--   Sparse Boxes: query Box iff is Largest
-- statement:
--   The Sparse Boxes construction uses the query Box iff is Largest property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L146-L151
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L146-L151

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

theorem ThreeSum.SparseBoxes.queryBox_iff_isLargest (q u leaf : Finset α) (t : ℕ)
    (huq : u ⊆ q) (huc : u.card = t) (hlq : leaf ⊆ q) :
    QueryBox q u leaf ↔ IsLargest t (q \ leaf) u := by sorry
