-- Prove2me | Theorems.Thm_Set_Infinite_exists_strictMono_range
-- name    : Set.Infinite.exists_strictMono_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:41:50.721785+00:00
-- url     : https://prove2.me/theorems/2fb0adf8-8efa-4d74-b568-72564b55f32b
-- title:
--   Infinite: exists strict Mono range
-- statement:
--   **Enumeration bridge.** Every infinite set of naturals is the range of its (unique) strictly
--   monotone enumeration. This recovers, from a set-valued carrier `X`, the enumeration `N` on which
--   the enumeration-first machinery (`Front.shrink`, ranks, …) operates.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Data/Nat/Nth.lean#L37-L42
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Data/Nat/Nth.lean#L37-L42

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

theorem Set.Infinite.exists_strictMono_range {X : Set ℕ} (hX : X.Infinite) :
    ∃ N : ℕ → ℕ, StrictMono N ∧ Set.range N = X := by sorry
