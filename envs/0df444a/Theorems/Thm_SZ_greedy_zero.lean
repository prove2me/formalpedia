-- Prove2me | Theorems.Thm_SZ_greedy_zero
-- name    : SZ.greedy_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:42:05.114925+00:00
-- url     : https://prove2.me/theorems/641db74d-0532-443a-b969-dd9d768fe21f
-- title:
--   SZ: greedy zero
-- statement:
--   The SZ construction uses the greedy zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Tijdeman.lean#L56-L56
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Tijdeman.lean#L56-L56

import Definitions.Def_SZ_Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_SZ_Tijdeman
set_option autoImplicit false
open SZ
variable {α : ℝ}

theorem SZ.greedy_zero (α : ℝ) : greedy α 0 = 2 := by sorry

attribute [defeq] SZ.greedy_zero
