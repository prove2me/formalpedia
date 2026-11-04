-- Prove2me | Theorems.Thm_ThreeSum_SparseBoxes_mem_explicitLeaves_w3sum_ac885d1
-- name    : ThreeSum.SparseBoxes.mem_explicitLeaves_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:15:52.69378+00:00
-- url     : https://prove2.me/theorems/2cdfdb73-0b04-4e37-912e-483879d7c0cc
-- title:
--   Sparse Boxes: mem explicit Leaves
-- statement:
--   The Sparse Boxes construction uses the mem explicit Leaves property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L549-L564
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L549-L564

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

theorem ThreeSum.SparseBoxes.mem_explicitLeaves_w3sum_ac885d1 (q leaf : Finset α) (t : ℕ) :
    leaf ∈ explicitLeaves q t ↔ leaf ⊆ q ∧ (q \ leaf).card < t := by sorry
