-- Prove2me | Theorems.Thm_ThreeSum_SparseBoxes_queryFree_eq_filter_min
-- name    : ThreeSum.SparseBoxes.queryFree_eq_filter_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:14:10.881958+00:00
-- url     : https://prove2.me/theorems/ace62f12-a1d9-4782-8892-065cc0520f7a
-- title:
--   Sparse Boxes: query Free eq filter min
-- statement:
--   The Sparse Boxes construction uses the query Free eq filter min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L98-L108
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L98-L108

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

theorem ThreeSum.SparseBoxes.queryFree_eq_filter_min (q u : Finset α) (hu : u.Nonempty) :
    queryFree q u = (q \ u).filter (fun x => x < u.min' hu) := by sorry
