-- Prove2me | Theorems.Thm_ThreeSum_Subset_fiberMass_conservation
-- name    : ThreeSum.Subset.fiberMass_conservation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:17:38.934138+00:00
-- url     : https://prove2.me/theorems/5e800857-77a1-4c25-82da-a76358b8e0ba
-- title:
--   Subset: fiber Mass conservation
-- statement:
--   Refinement into all allowed next labels preserves the original weighted
--   mass, including multiplicity. This is a finite-sum identity, not a bound assumed
--   from the proposed 3SUM algorithm.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L483-L488
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L483-L488

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

theorem ThreeSum.Subset.fiberMass_conservation {β γ : Type*} [DecidableEq γ]
    (domain : Finset β) (labels : Finset γ) (label : β → γ) (weight : β → ℕ)
    (hlabels : ∀ p ∈ domain, label p ∈ labels) :
    (∑ value ∈ labels, fiberMass domain label weight value) =
      ∑ p ∈ domain, weight p := by sorry
