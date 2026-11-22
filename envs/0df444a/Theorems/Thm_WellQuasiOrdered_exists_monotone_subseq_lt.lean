-- Prove2me | Theorems.Thm_WellQuasiOrdered_exists_monotone_subseq_lt
-- name    : WellQuasiOrdered.exists_monotone_subseq_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:54.583074+00:00
-- url     : https://prove2.me/theorems/b74f3ede-bd84-4f5a-bf9c-36df0f4e1c91
-- title:
--   Well Quasi Ordered: exists monotone subseq lt
-- statement:
--   **Monotone subsequences from a WQO, without transitivity.** In a well-quasi-order, every
--   sequence has a strictly increasing reindexing `e` along which `r (f (e m)) (f (e n))` holds for
--   all `m < n`. Follows directly from the perfect/bad dichotomy: a bad subsequence would contradict
--   the WQO. No typeclass assumptions on `r`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/WellQuasiOrder/Basic.lean#L80-L85
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/WellQuasiOrder/Basic.lean#L80-L85

module
public import Mathlib.Order.WellQuasiOrder
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Ramsey_Infinite
public import Definitions.Def_LeanPool_NashWilliams_Order_WellQuasiOrder_Basic
set_option autoImplicit true
@[expose] public section
public section
open Set
noncomputable section
open Sequences
variable {α : Type*} {r : α → α → Prop}

theorem WellQuasiOrdered.exists_monotone_subseq_lt (h : WellQuasiOrdered r) (f : ℕ → α) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∀ m n : ℕ, m < n → r (f (e m)) (f (e n)) := by sorry
