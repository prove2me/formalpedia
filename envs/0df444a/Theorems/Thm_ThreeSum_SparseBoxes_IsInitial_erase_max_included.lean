-- Prove2me | Theorems.Thm_ThreeSum_SparseBoxes_IsInitial_erase_max_included
-- name    : ThreeSum.SparseBoxes.IsInitial.erase_max_included
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:14:19.014197+00:00
-- url     : https://prove2.me/theorems/9b9ce27b-ddc9-4780-b4d5-618a9b78f0f3
-- title:
--   Is Initial: erase max included
-- statement:
--   Removing the greatest free coordinate preserves the canonical-family
--   condition in the included child.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L233-L246
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L233-L246

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

theorem ThreeSum.SparseBoxes.IsInitial.erase_max_included {flags free : Finset α}
    (h : IsInitial flags free) (hn : free.Nonempty) :
    IsInitial flags (free.erase (free.max' hn)) := by sorry
