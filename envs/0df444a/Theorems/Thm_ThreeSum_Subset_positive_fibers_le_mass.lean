-- Prove2me | Theorems.Thm_ThreeSum_Subset_positive_fibers_le_mass
-- name    : ThreeSum.Subset.positive_fibers_le_mass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:17:37.676196+00:00
-- url     : https://prove2.me/theorems/9d769413-c630-4e97-a36c-2d6f9e2fe542
-- title:
--   Subset: positive fibers le mass
-- statement:
--   A positive child has integer mass at least one, so the number of positive
--   children cannot exceed the parent's mass.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L492-L506
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L492-L506

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

theorem ThreeSum.Subset.positive_fibers_le_mass {β γ : Type*} [DecidableEq γ]
    (domain : Finset β) (labels : Finset γ) (label : β → γ) (weight : β → ℕ)
    (hlabels : ∀ p ∈ domain, label p ∈ labels) :
    (labels.filter (fun value => 0 < fiberMass domain label weight value)).card ≤
      ∑ p ∈ domain, weight p := by sorry
