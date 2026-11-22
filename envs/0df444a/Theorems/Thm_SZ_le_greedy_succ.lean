-- Prove2me | Theorems.Thm_SZ_le_greedy_succ
-- name    : SZ.le_greedy_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:42:16.028548+00:00
-- url     : https://prove2.me/theorems/90eef8a9-261b-4058-a63a-5c3374fadf10
-- title:
--   SZ: le greedy succ
-- statement:
--   The greedy never falls below `α` times its predecessor.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Tijdeman.lean#L67-L70
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Tijdeman.lean#L67-L70

import Definitions.Def_SZ_Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_SZ_Tijdeman
set_option autoImplicit false
open SZ
variable {α : ℝ}

theorem SZ.le_greedy_succ (α : ℝ) (n : ℕ) :
    α * (greedy α n : ℝ) ≤ (greedy α (n + 1) : ℝ) := by sorry
