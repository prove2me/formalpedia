-- Prove2me | Theorems.Thm_SZ_gHi_anti
-- name    : SZ.gHi_anti
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:49:50.610796+00:00
-- url     : https://prove2.me/theorems/71a5dd24-9c63-4abf-91a7-11edde20d317
-- title:
--   SZ: g Hi anti
-- statement:
--   The SZ construction uses the g Hi anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Tijdeman.lean#L114-L115
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Tijdeman.lean#L114-L115

import Definitions.Def_SZ_Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_SZ_Tijdeman
set_option autoImplicit false
open SZ
variable {α : ℝ}

theorem SZ.gHi_anti (hα : 3 ≤ α) : Antitone (gHi α) := by sorry
