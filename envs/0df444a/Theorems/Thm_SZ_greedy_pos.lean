-- Prove2me | Theorems.Thm_SZ_greedy_pos
-- name    : SZ.greedy_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:53:24.150773+00:00
-- url     : https://prove2.me/theorems/7d5673ca-515b-4c3a-8dfe-bd9b9af9f828
-- title:
--   SZ: greedy pos
-- statement:
--   The SZ construction uses the greedy pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Tijdeman.lean#L78-L83
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Tijdeman.lean#L78-L83

import Definitions.Def_SZ_Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_SZ_Tijdeman
set_option autoImplicit false
open SZ
variable {α : ℝ}

theorem SZ.greedy_pos (hα : 3 ≤ α) (n : ℕ) : 0 < (greedy α n : ℝ) := by sorry
