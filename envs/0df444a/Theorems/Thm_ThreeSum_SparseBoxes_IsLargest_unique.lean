-- Prove2me | Theorems.Thm_ThreeSum_SparseBoxes_IsLargest_unique
-- name    : ThreeSum.SparseBoxes.IsLargest.unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:22:40.498216+00:00
-- url     : https://prove2.me/theorems/61f45030-c452-4636-b2fb-f148af7677ba
-- title:
--   Is Largest: unique
-- statement:
--   The Is Largest construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L70-L84
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L70-L84

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

theorem ThreeSum.SparseBoxes.IsLargest.unique {t : ℕ} {m u v : Finset α}
    (hu : IsLargest t m u) (hv : IsLargest t m v) : u = v := by sorry
