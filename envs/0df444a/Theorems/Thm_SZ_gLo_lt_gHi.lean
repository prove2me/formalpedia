-- Prove2me | Theorems.Thm_SZ_gLo_lt_gHi
-- name    : SZ.gLo_lt_gHi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:49:56.346295+00:00
-- url     : https://prove2.me/theorems/090109ee-3028-40c7-bba5-1a79f24c3622
-- title:
--   SZ: g Lo lt g Hi
-- statement:
--   The SZ construction uses the g Lo lt g Hi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Tijdeman.lean#L117-L121
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Tijdeman.lean#L117-L121

import Definitions.Def_SZ_Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_SZ_Tijdeman
set_option autoImplicit false
open SZ
variable {α : ℝ}

theorem SZ.gLo_lt_gHi (hα : 3 ≤ α) (n : ℕ) : gLo α n < gHi α n := by sorry
