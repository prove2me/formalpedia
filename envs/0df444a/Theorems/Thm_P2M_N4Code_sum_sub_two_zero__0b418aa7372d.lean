-- Prove2me | Theorems.Thm_P2M_N4Code_sum_sub_two_zero__0b418aa7372d
-- name    : P2M_N4Code_sum_sub_two_zero__0b418aa7372d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:18:11.680557+00:00
-- url     : https://prove2.me/theorems/dea1a5b4-63aa-4737-aa76-aa2733e7ab47
-- title:
--   P2 M N4 Code sum sub two zero  0b418aa7372d: P2 M N4 Code sum sub two zero  0b418aa7372d
-- statement:
--   If two functions agree off {t₁,t₂}, the first is one larger at t₁ and one
--   smaller at t₂, then the sums are equal.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L96-L130
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L96-L130

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem P2M_N4Code_sum_sub_two_zero__0b418aa7372d {n : ℕ} (f g : Fin n → ℕ) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : f t₁ = g t₁ + 1) (h2 : f t₂ + 1 = g t₂)
    (hrest : ∀ u : Fin n, u ≠ t₁ → u ≠ t₂ → f u = g u) :
    (∑ u : Fin n, f u) = (∑ u : Fin n, g u) := by sorry

alias «N4Code».«sum_sub_two_zero₁» := P2M_N4Code_sum_sub_two_zero__0b418aa7372d
