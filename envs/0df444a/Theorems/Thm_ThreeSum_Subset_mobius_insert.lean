-- Prove2me | Theorems.Thm_ThreeSum_Subset_mobius_insert
-- name    : ThreeSum.Subset.mobius_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:17:19.042047+00:00
-- url     : https://prove2.me/theorems/8ebb6314-5bbb-410f-abd2-ecfc67347f93
-- title:
--   Subset: mobius insert
-- statement:
--   The Subset construction uses the mobius insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L50-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L50-L78

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import Lean.Elab.Tactic.Omega
import Aesop
import Definitions.Def_Submission_ThreeSum_Subset
set_option autoImplicit false
open ThreeSum ThreeSum.Subset
open scoped BigOperators
variable {α : Type*} [DecidableEq α]

theorem ThreeSum.Subset.mobius_insert (f : Finset α → ℤ) {q : Finset α} {a : α}
    (ha : a ∉ q) :
    mobius f (insert a q) =
      mobius (fun s => f (insert a s)) q - mobius f q := by sorry
