-- Prove2me | Theorems.Thm_ThreeSum_Subset_fixed_cardinality_identity_nat
-- name    : ThreeSum.Subset.fixed_cardinality_identity_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:17:23.559535+00:00
-- url     : https://prove2.me/theorems/6f493624-c873-4790-800b-120645841231
-- title:
--   Subset: fixed cardinality identity nat
-- statement:
--   For histogram populations the signed expression is exactly a natural-number
--   count, embedded into the integers; no positivity of an intermediate box sum is
--   assumed.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L257-L279
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L257-L279

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

theorem ThreeSum.Subset.fixed_cardinality_identity_nat
    (f g : Finset α → ℕ) (q : Finset α) (a b : ℕ)
    (hf : ∀ s, f s ≠ 0 → s.card = a)
    (hg : ∀ v, g v ≠ 0 → v.card = b)
    (hq : q.card = a + b) :
    (∑ t ∈ q.powerset, (-1 : ℤ) ^ (q.card - t.card) *
      (∑ s ∈ t.powerset, (f s : ℤ)) * (∑ v ∈ t.powerset, (g v : ℤ))) =
    (∑ s ∈ q.powerset, f s * g (q \ s) : ℕ) := by sorry
