-- Prove2me | Theorems.Thm_SZ_rec2_add_two
-- name    : SZ.rec2_add_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:41:50.111977+00:00
-- url     : https://prove2.me/theorems/aac13fc7-9542-4af3-adda-29188d2913d3
-- title:
--   SZ: rec2 add two
-- statement:
--   The SZ construction uses the rec2 add two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Trace.lean#L59-L60
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Trace.lean#L59-L60

import Definitions.Def_SZ_Defs
import Mathlib.Tactic.LinearCombination
import Definitions.Def_SZ_Trace
set_option autoImplicit false
open SZ

theorem SZ.rec2_add_two (A B t₀ t₁ : ℤ) (n : ℕ) :
    rec2 A B t₀ t₁ (n + 2) = A * rec2 A B t₀ t₁ (n + 1) + B * rec2 A B t₀ t₁ n := by sorry
