-- Prove2me | Theorems.Thm_ThreeSum_SparseBoxes_records_card_layers
-- name    : ThreeSum.SparseBoxes.records_card_layers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:14:22.393169+00:00
-- url     : https://prove2.me/theorems/2519bbd3-3037-442a-bb8c-4df9586a822c
-- title:
--   Sparse Boxes: records card layers
-- statement:
--   The Sparse Boxes construction uses the records card layers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L294-L311
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SparseBoxes.lean#L294-L311

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

theorem ThreeSum.SparseBoxes.records_card_layers (ambient : Finset α) (cut : ℕ) :
    (records ambient cut).card =
      ∑ j ∈ Finset.range (ambient.card + 1),
        if j ≤ cut then (j + 1) * ambient.card.choose j else 0 := by sorry
