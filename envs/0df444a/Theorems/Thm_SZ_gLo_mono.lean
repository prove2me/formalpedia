-- Prove2me | Theorems.Thm_SZ_gLo_mono
-- name    : SZ.gLo_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:49:45.783254+00:00
-- url     : https://prove2.me/theorems/331f802e-05a4-4ec1-b5e9-7381bda9d07f
-- title:
--   SZ: g Lo mono
-- statement:
--   The SZ construction uses the g Lo mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Tijdeman.lean#L93-L100
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Tijdeman.lean#L93-L100

import Definitions.Def_SZ_Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_SZ_Tijdeman
set_option autoImplicit false
open SZ
variable {α : ℝ}

theorem SZ.gLo_mono (hα : 3 ≤ α) : Monotone (gLo α) := by sorry
