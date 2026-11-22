-- Prove2me | Theorems.Thm_SZ_floor_greedy
-- name    : SZ.floor_greedy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:50:36.336159+00:00
-- url     : https://prove2.me/theorems/d464f415-6852-4adc-8ac6-b79bc5b78ef0
-- title:
--   SZ: floor greedy
-- statement:
--   **The floors of the witness orbit are the greedy sequence.**
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Tijdeman.lean#L143-L152
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Tijdeman.lean#L143-L152

import Definitions.Def_SZ_Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_SZ_Tijdeman
set_option autoImplicit false
open SZ
variable {α : ℝ}

theorem SZ.floor_greedy (hα : 3 ≤ α) (n : ℕ) :
    ⌊tijdemanWitness α * α ^ n⌋ = greedy α n := by sorry
