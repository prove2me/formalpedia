-- Prove2me | Theorems.Thm_ThreeSum_Subset_balanced_block_refinement_conservation
-- name    : ThreeSum.Subset.balanced_block_refinement_conservation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:17:38.807189+00:00
-- url     : https://prove2.me/theorems/2d673710-ed43-4aec-ac27-3f4b9ac15f47
-- title:
--   Subset: balanced block refinement conservation
-- statement:
--   The algorithm visits only balanced assignments. If every completion has
--   exactly `h` positions in the next block, the balanced children still partition
--   all of the weighted mass.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L523-L532
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L523-L532

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

theorem ThreeSum.Subset.balanced_block_refinement_conservation
    (completions : Finset (Finset α)) (block : Finset α) (h : ℕ)
    (weight : Finset α → ℕ)
    (hbalanced : ∀ s ∈ completions, (s ∩ block).card = h) :
    (∑ child ∈ block.powersetCard h,
      fiberMass completions (fun s => s ∩ block) weight child) =
      ∑ s ∈ completions, weight s := by sorry
