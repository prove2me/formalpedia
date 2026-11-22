-- Prove2me | Theorems.Thm_SZ_greedy_even
-- name    : SZ.greedy_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:48:51.74085+00:00
-- url     : https://prove2.me/theorems/2b9c69aa-9993-4abd-a718-96c1c99d9257
-- title:
--   SZ: greedy even
-- statement:
--   The SZ construction uses the greedy even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Tijdeman.lean#L61-L64
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Tijdeman.lean#L61-L64

import Definitions.Def_SZ_Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_SZ_Tijdeman
set_option autoImplicit false
open SZ
variable {α : ℝ}

theorem SZ.greedy_even (α : ℝ) (n : ℕ) : Even (greedy α n) := by sorry
