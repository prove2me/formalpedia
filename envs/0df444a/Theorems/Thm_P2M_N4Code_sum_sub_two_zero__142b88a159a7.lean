-- Prove2me | Theorems.Thm_P2M_N4Code_sum_sub_two_zero__142b88a159a7
-- name    : P2M_N4Code_sum_sub_two_zero__142b88a159a7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:19:20.807857+00:00
-- url     : https://prove2.me/theorems/ca8c546e-02a9-48d4-b545-49f637c71916
-- title:
--   P2 M N4 Code sum sub two zero  142b88a159a7: P2 M N4 Code sum sub two zero  142b88a159a7
-- statement:
--   If two functions agree off {t₁,t₂}, the first is one smaller at t₁ and one
--   larger at t₂, then the sums are equal.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L134-L139
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L134-L139

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem P2M_N4Code_sum_sub_two_zero__142b88a159a7 {n : ℕ} (f g : Fin n → ℕ) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : f t₁ + 1 = g t₁) (h2 : f t₂ = g t₂ + 1)
    (hrest : ∀ u : Fin n, u ≠ t₁ → u ≠ t₂ → f u = g u) :
    (∑ u : Fin n, f u) = (∑ u : Fin n, g u) := by sorry

alias «N4Code».«sum_sub_two_zero₂» := P2M_N4Code_sum_sub_two_zero__142b88a159a7
