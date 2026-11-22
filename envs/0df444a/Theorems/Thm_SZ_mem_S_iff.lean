-- Prove2me | Theorems.Thm_SZ_mem_S_iff
-- name    : SZ.mem_S_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:41:13.93626+00:00
-- url     : https://prove2.me/theorems/e986cdce-e04c-40ac-a7a6-98c708cb82ae
-- title:
--   SZ: mem S iff
-- statement:
--   The SZ construction uses the mem S iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Defs.lean#L72-L72
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Defs.lean#L72-L72

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

theorem SZ.mem_S_iff {α : ℝ} : α ∈ S ↔ 1 < α ∧ α ∉ MahlerZ := by sorry
