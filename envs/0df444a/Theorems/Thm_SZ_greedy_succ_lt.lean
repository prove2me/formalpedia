-- Prove2me | Theorems.Thm_SZ_greedy_succ_lt
-- name    : SZ.greedy_succ_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:49:36.042821+00:00
-- url     : https://prove2.me/theorems/84cc8e73-5925-4ff4-a057-db5d8a6c5d53
-- title:
--   SZ: greedy succ lt
-- statement:
--   …and it overshoots by less than `2`.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Tijdeman.lean#L73-L76
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Tijdeman.lean#L73-L76

import Definitions.Def_SZ_Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_SZ_Tijdeman
set_option autoImplicit false
open SZ
variable {α : ℝ}

theorem SZ.greedy_succ_lt (α : ℝ) (n : ℕ) :
    (greedy α (n + 1) : ℝ) < α * (greedy α n : ℝ) + 2 := by sorry
