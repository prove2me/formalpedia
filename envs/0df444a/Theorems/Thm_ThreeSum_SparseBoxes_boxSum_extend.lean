-- Prove2me | Theorems.Thm_ThreeSum_SparseBoxes_boxSum_extend
-- name    : ThreeSum.SparseBoxes.boxSum_extend
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:15:49.132852+00:00
-- url     : https://prove2.me/theorems/ad71a61c-a583-47c8-9576-83c91021ae24
-- title:
--   Sparse Boxes: box Sum extend
-- statement:
--   The Sparse Boxes construction uses the box Sum extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L361-L381
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L361-L381

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

theorem ThreeSum.SparseBoxes.boxSum_extend (ambient flags free : Finset α) (weight : Finset α → ℤ)
    (hf : flags ⊆ ambient) :
    boxSum flags free weight =
      ∑ leaf ∈ ambient.powerset,
        if BoxMember flags free leaf then weight leaf else 0 := by sorry
