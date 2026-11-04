-- Prove2me | Theorems.Thm_ThreeSum_Subset_block_refinement_conservation
-- name    : ThreeSum.Subset.block_refinement_conservation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:17:40.595159+00:00
-- url     : https://prove2.me/theorems/2d4288d5-6a82-4fee-87bc-c6c87d4a10be
-- title:
--   Subset: block refinement conservation
-- statement:
--   Revealing a block means classifying a completion by its intersection with
--   that block. Summing all resulting subset fibers preserves mass.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L510-L518
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L510-L518

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

theorem ThreeSum.Subset.block_refinement_conservation
    (completions : Finset (Finset α)) (block : Finset α)
    (weight : Finset α → ℕ) :
    (∑ child ∈ block.powerset,
      fiberMass completions (fun s => s ∩ block) weight child) =
      ∑ s ∈ completions, weight s := by sorry
