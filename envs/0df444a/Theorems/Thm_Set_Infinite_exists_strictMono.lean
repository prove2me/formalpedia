-- Prove2me | Theorems.Thm_Set_Infinite_exists_strictMono
-- name    : Set.Infinite.exists_strictMono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:41:45.868331+00:00
-- url     : https://prove2.me/theorems/57e175f0-6cbb-450a-8268-af522cbfa02c
-- title:
--   Infinite: exists strict Mono
-- statement:
--   The membership form of `Set.Infinite.exists_strictMono_range`: an infinite set of naturals
--   carries a strictly monotone sequence of its elements.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Data/Nat/Nth.lean#L46-L49
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Data/Nat/Nth.lean#L46-L49

module
public import Aesop.BuiltinRules
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Data.Nat.Nth
public import Definitions.Def_LeanPool_NashWilliams_Data_Nat_Nth
set_option autoImplicit true
@[expose] public section
public section

theorem Set.Infinite.exists_strictMono {s : Set ℕ} (hs : s.Infinite) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∀ i, e i ∈ s := by sorry
