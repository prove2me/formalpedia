-- Prove2me | Theorems.Thm_WellQuasiOrdered_exists_forall_le_of_antitone
-- name    : WellQuasiOrdered.exists_forall_le_of_antitone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:10.922872+00:00
-- url     : https://prove2.me/theorems/c13d6abb-4ddd-40cc-8b86-db4bd5d89c97
-- title:
--   Well Quasi Ordered: exists forall le of antitone
-- statement:
--   In a WQO, an antitone sequence stabilizes from above: there is an index `m` from
--   which the sequence becomes `r`-dominated by `a m` (so, together with antitonicity,
--   `a m` is `r`-equivalent to every later term).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/WellQuasiOrder/Regular.lean#L147-L161
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/WellQuasiOrder/Regular.lean#L147-L161

module
public import Mathlib.Order.WellQuasiOrder
public import Mathlib.Order.WellFoundedSet
public import Definitions.Def_LeanPool_NashWilliams_Order_WellQuasiOrder_Regular
set_option autoImplicit true
@[expose] public section
public section
open Set Preorder
noncomputable section

theorem WellQuasiOrdered.exists_forall_le_of_antitone {β : Type*} {r : β → β → Prop}
    [IsPreorder β r] (hwqo : WellQuasiOrdered r) (a : ℕ → β)
    (hanti : ∀ m n : ℕ, m ≤ n → r (a n) (a m)) :
    ∃ m : ℕ, ∀ n : ℕ, m ≤ n → r (a m) (a n) := by sorry
