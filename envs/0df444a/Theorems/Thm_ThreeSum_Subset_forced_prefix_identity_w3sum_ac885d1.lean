-- Prove2me | Theorems.Thm_ThreeSum_Subset_forced_prefix_identity_w3sum_ac885d1
-- name    : ThreeSum.Subset.forced_prefix_identity_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:17:39.333902+00:00
-- url     : https://prove2.me/theorems/f335d7eb-a26a-43b7-a009-65154063e82d
-- title:
--   Subset: forced prefix identity
-- statement:
--   The restricted count used by a reporting query is obtained from the already
--   stored partial-zeta stages.  No extra restricted transform is postulated.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L442-L471
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L442-L471

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

theorem ThreeSum.Subset.forced_prefix_identity_w3sum_ac885d1
    (f g : Finset α → ℤ) (prefix₁ prefix₂ suffix q : Finset α) (a b : ℕ)
    (hf : ∀ s, f s ≠ 0 → s.card = a)
    (hg : ∀ v, g v ≠ 0 → v.card = b)
    (hd₁ : Disjoint prefix₁ suffix) (hd₂ : Disjoint prefix₂ suffix)
    (hqs : q ⊆ suffix)
    (hq : q.card = (a - prefix₁.card) + (b - prefix₂.card)) :
    mobius (fun t => partialZeta suffix f (prefix₁ ∪ t) *
      partialZeta suffix g (prefix₂ ∪ t)) q =
    ∑ x ∈ q.powerset, f (prefix₁ ∪ x) * g (prefix₂ ∪ (q \ x)) := by sorry
