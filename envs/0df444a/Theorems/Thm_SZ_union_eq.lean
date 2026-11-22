-- Prove2me | Theorems.Thm_SZ_union_eq
-- name    : SZ.union_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:41:13.509256+00:00
-- url     : https://prove2.me/theorems/24245ee2-08c7-4dbf-a5e7-cce9f807f5d9
-- title:
--   SZ: union eq
-- statement:
--   The SZ construction uses the union eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Defs.lean#L74-L77
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Defs.lean#L74-L77

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

theorem SZ.union_eq {α : ℝ} (hα : 1 < α) : α ∈ MahlerZ ∨ α ∈ S := by sorry
