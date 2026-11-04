-- Prove2me | Theorems.Thm_ThreeSum_SparseBoxes_explicitLeaves_eq_filter
-- name    : ThreeSum.SparseBoxes.explicitLeaves_eq_filter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:15:53.81875+00:00
-- url     : https://prove2.me/theorems/a2c474f0-4fa6-4349-af7c-f089f46ba8b6
-- title:
--   Sparse Boxes: explicit Leaves eq filter
-- statement:
--   The Sparse Boxes construction uses the explicit Leaves eq filter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L566-L569
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L566-L569

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

theorem ThreeSum.SparseBoxes.explicitLeaves_eq_filter (q : Finset α) (t : ℕ) :
    explicitLeaves q t = q.powerset.filter (fun leaf => (q \ leaf).card < t) := by sorry
