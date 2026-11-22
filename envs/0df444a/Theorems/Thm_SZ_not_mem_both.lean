-- Prove2me | Theorems.Thm_SZ_not_mem_both
-- name    : SZ.not_mem_both
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:41:15.959881+00:00
-- url     : https://prove2.me/theorems/d76df675-fe14-48ef-80cc-a21c08266e13
-- title:
--   SZ: not mem both
-- statement:
--   The SZ construction uses the not mem both property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Defs.lean#L79-L79
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Defs.lean#L79-L79

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Defs
set_option autoImplicit false
open SZ
open Int

theorem SZ.not_mem_both {α : ℝ} : ¬ (α ∈ MahlerZ ∧ α ∈ S) := by sorry
