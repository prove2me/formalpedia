-- Prove2me | Theorems.Thm_Sequences_perfect_or_bad
-- name    : Sequences.perfect_or_bad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:33.969882+00:00
-- url     : https://prove2.me/theorems/6be032fb-1d30-4ed8-b9e4-66cf883e2722
-- title:
--   Sequences: perfect or bad
-- statement:
--   **Perfect/bad dichotomy.** Every sequence `f : ℕ → α` has a strictly increasing reindexing
--   `f ∘ e` that is either perfect or bad for `r`. Immediate from the infinite Ramsey theorem for
--   pairs applied to the `2`-colouring `(m, n) ↦ ¬ r (f m) (f n)`; no order axioms are used.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/WellQuasiOrder/Basic.lean#L52-L68
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/WellQuasiOrder/Basic.lean#L52-L68

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
variable {α : Type*}

theorem Sequences.perfect_or_bad (r : α → α → Prop) (f : ℕ → α) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ (IsPerfect r (f ∘ e) ∨ IsBad r (f ∘ e)) := by sorry
