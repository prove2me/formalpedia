-- Prove2me | Theorems.Thm_ThreeSum_SparseBoxes_records_card_bound
-- name    : ThreeSum.SparseBoxes.records_card_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:22:03.236329+00:00
-- url     : https://prove2.me/theorems/b4a15c3f-0ff8-4529-b1ea-4b7cd28b9aa2
-- title:
--   Sparse Boxes: records card bound
-- statement:
--   The complete box-family size is a polynomial factor times its final
--   binomial layer, as used in the written preprocessing bound.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L328-L345
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L328-L345

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

theorem ThreeSum.SparseBoxes.records_card_bound (ambient : Finset α) (cut : ℕ)
    (hcut : cut ≤ ambient.card / 2) :
    (records ambient cut).card ≤
      (ambient.card + 1) ^ 2 * ambient.card.choose cut := by sorry
