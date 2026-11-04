-- Prove2me | Theorems.Thm_ThreeSum_Subset_fixed_cardinality_identity
-- name    : ThreeSum.Subset.fixed_cardinality_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:17:24.943343+00:00
-- url     : https://prove2.me/theorems/50fb805c-c408-4cf2-9516-fbb1cc86c185
-- title:
--   Subset: fixed cardinality identity
-- statement:
--   The complete fixed-cardinality Möbius/subset-convolution identity.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L242-L252
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L242-L252

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

theorem ThreeSum.Subset.fixed_cardinality_identity
    (f g : Finset α → ℤ) (q : Finset α) (a b : ℕ)
    (hf : ∀ s, f s ≠ 0 → s.card = a)
    (hg : ∀ v, g v ≠ 0 → v.card = b)
    (hq : q.card = a + b) :
    (∑ t ∈ q.powerset, (-1 : ℤ) ^ (q.card - t.card) *
      (∑ s ∈ t.powerset, f s) * (∑ v ∈ t.powerset, g v)) =
    ∑ s ∈ q.powerset, f s * g (q \ s) := by sorry
