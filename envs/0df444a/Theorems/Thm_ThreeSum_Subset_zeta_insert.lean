-- Prove2me | Theorems.Thm_ThreeSum_Subset_zeta_insert
-- name    : ThreeSum.Subset.zeta_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:14:16.111822+00:00
-- url     : https://prove2.me/theorems/2d8ca7ca-1f48-4c5b-b26f-6766f72aec51
-- title:
--   Subset: zeta insert
-- statement:
--   The Subset construction uses the zeta insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L35-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L35-L38

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

theorem ThreeSum.Subset.zeta_insert (f : Finset α → ℤ) {q : Finset α} {a : α}
    (ha : a ∉ q) :
    zeta f (insert a q) = zeta f q + zeta (fun s => f (insert a s)) q := by sorry
