-- Prove2me | Theorems.Thm_ThreeSum_Subset_forced_prefix_stays_in_downset
-- name    : ThreeSum.Subset.forced_prefix_stays_in_downset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:17:34.293396+00:00
-- url     : https://prove2.me/theorems/732f4b0b-bcf9-4f0f-b126-3684b4277e3c
-- title:
--   Subset: forced prefix stays in downset
-- statement:
--   Every lookup of the forced-pre formula lies in the stored downset
--   whenever the total pre-plus-suffix size is at most `mu`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L394-L397
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L394-L397

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

theorem ThreeSum.Subset.forced_prefix_stays_in_downset
    (s₀ t : Finset α) (mu : ℕ) (h : s₀.card + t.card ≤ mu) :
    (s₀ ∪ t).card ≤ mu := by sorry
