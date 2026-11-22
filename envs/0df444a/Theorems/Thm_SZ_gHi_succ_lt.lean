-- Prove2me | Theorems.Thm_SZ_gHi_succ_lt
-- name    : SZ.gHi_succ_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:47:26.336487+00:00
-- url     : https://prove2.me/theorems/3a132930-10db-4d78-b722-7d3047ffdb76
-- title:
--   SZ: g Hi succ lt
-- statement:
--   The upper ends drop strictly — this is exactly where `α ≥ 3` is spent: the greedy
--   overshoots by less than `2`, and `2 + 1 ≤ α`.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Tijdeman.lean#L104-L112
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Tijdeman.lean#L104-L112

import Definitions.Def_SZ_Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_SZ_Tijdeman
set_option autoImplicit false
open SZ
variable {α : ℝ}

theorem SZ.gHi_succ_lt (hα : 3 ≤ α) (n : ℕ) : gHi α (n + 1) < gHi α n := by sorry
