-- Prove2me | Theorems.Thm_ThreeSum_Subset_partialZeta_insert_w3sum_ac885d1
-- name    : ThreeSum.Subset.partialZeta_insert_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:17:31.140382+00:00
-- url     : https://prove2.me/theorems/0c26492c-c1c6-4120-b499-f062d9158d1d
-- title:
--   Subset: partial Zeta insert
-- statement:
--   The exact update invariant for the ordinary coordinatewise zeta DP.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L301-L346
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L301-L346

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

theorem ThreeSum.Subset.partialZeta_insert_w3sum_ac885d1 (f : Finset α → ℤ) (u processed : Finset α)
    (a : α) (ha : a ∉ processed) :
    partialZeta (insert a processed) f u =
      zetaStep a (partialZeta processed f) u := by sorry
