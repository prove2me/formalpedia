-- Prove2me | Theorems.Thm_SZ_gLo_bddAbove
-- name    : SZ.gLo_bddAbove
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:50:01.48419+00:00
-- url     : https://prove2.me/theorems/0a433d0b-2364-4269-93b0-808a26a2b02b
-- title:
--   SZ: g Lo bdd Above
-- statement:
--   The SZ construction uses the g Lo bdd Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Tijdeman.lean#L131-L134
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Tijdeman.lean#L131-L134

import Definitions.Def_SZ_Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_SZ_Tijdeman
set_option autoImplicit false
open SZ
variable {α : ℝ}

theorem SZ.gLo_bddAbove (hα : 3 ≤ α) : BddAbove (Set.range (gLo α)) := by sorry
