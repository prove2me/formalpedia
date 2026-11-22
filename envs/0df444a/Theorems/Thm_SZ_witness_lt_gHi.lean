-- Prove2me | Theorems.Thm_SZ_witness_lt_gHi
-- name    : SZ.witness_lt_gHi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:50:08.406276+00:00
-- url     : https://prove2.me/theorems/1e14b616-b8a3-426b-88ba-179d6d1309b5
-- title:
--   SZ: witness lt g Hi
-- statement:
--   The SZ construction uses the witness lt g Hi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Tijdeman.lean#L139-L140
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Tijdeman.lean#L139-L140

import Definitions.Def_SZ_Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_SZ_Tijdeman
set_option autoImplicit false
open SZ
variable {α : ℝ}

theorem SZ.witness_lt_gHi (hα : 3 ≤ α) (n : ℕ) : tijdemanWitness α < gHi α n := by sorry
