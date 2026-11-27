-- Prove2me | Theorems.Thm_RamanujanNested_rollUpN_bounded
-- name    : RamanujanNested.rollUpN_bounded
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-27T05:11:09.845525+00:00
-- url     : https://prove2.me/theorems/968b9b82-8344-4700-b644-949826eaa67d
-- title:
--   Ramanujan Nested: roll Up N bounded
-- statement:
--   **Boundedness, general root order.** Given a ceiling `r` compatible with
--   `A` in the sense `(1+A*r)^(1/n) ≤ r`, every truncation of the n-th-root
--   radical (with `0 ≤ a_k ≤ A` and seed `T ∈ [0, r]`) stays in `[0, r]`. Stated
--   with the compatibility hypothesis directly in `rpow` form so the induction
--   itself never needs to convert between `rpow` and ordinary `pow` — that
--   conversion is confined to `exists_ceiling_rpow` below, where a concrete `r`
--   is produced.
--
--   Source: https://github.com/Flaman55/RamanujanNestedRadicals/blob/2b932baf2e72426583ef47a1bb23b4458879e959/RamanujanNested/NthRootChain.lean#L82-L107
-- source:
--   https://github.com/Flaman55/RamanujanNestedRadicals/blob/2b932baf2e72426583ef47a1bb23b4458879e959/RamanujanNested/NthRootChain.lean#L82-L107

module
public import Definitions.Def_RamanujanNested_Defs
public import Mathlib
public import Definitions.Def_RamanujanNested_NthRootChain
set_option autoImplicit true
@[expose] public section
open RamanujanNested

theorem RamanujanNested.rollUpN_bounded {n : ℕ} {A r : ℝ} (hA : 0 ≤ A)
    (hceil : (1 + A * r) ^ (1 / (n : ℝ)) ≤ r) :
    ∀ (d : ℕ) (T : ℝ) (a : ℕ → ℝ), 0 ≤ T → T ≤ r → (∀ k, 0 ≤ a k) → (∀ k, a k ≤ A) →
      0 ≤ rollUpN n a T d ∧ rollUpN n a T d ≤ r := by sorry
