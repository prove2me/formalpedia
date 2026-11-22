-- Prove2me | Theorems.Thm_SZ_greedy_succ
-- name    : SZ.greedy_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:42:10.211838+00:00
-- url     : https://prove2.me/theorems/bdcdbb1e-e99b-4cf9-8e9f-ea3fbc78675e
-- title:
--   SZ: greedy succ
-- statement:
--   The SZ construction uses the greedy succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Tijdeman.lean#L58-L59
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Tijdeman.lean#L58-L59

import Definitions.Def_SZ_Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_SZ_Tijdeman
set_option autoImplicit false
open SZ
variable {α : ℝ}

theorem SZ.greedy_succ (α : ℝ) (n : ℕ) :
    greedy α (n + 1) = 2 * ⌈α * (greedy α n : ℝ) / 2⌉ := by sorry
