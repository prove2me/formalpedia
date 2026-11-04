-- Prove2me | Theorems.Thm_ThreeSum_SparseBoxes_IsInitial_erase_max_excluded
-- name    : ThreeSum.SparseBoxes.IsInitial.erase_max_excluded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:14:20.31769+00:00
-- url     : https://prove2.me/theorems/f45f0e96-ea2e-45a1-89b9-54fd40f4789f
-- title:
--   Is Initial: erase max excluded
-- statement:
--   The excluded child removes that same coordinate from its flags.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L249-L257
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L249-L257

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

theorem ThreeSum.SparseBoxes.IsInitial.erase_max_excluded {flags free : Finset α}
    (h : IsInitial flags free) (hn : free.Nonempty) :
    IsInitial (flags.erase (free.max' hn)) (free.erase (free.max' hn)) := by sorry
