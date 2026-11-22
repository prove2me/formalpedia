-- Prove2me | Theorems.Thm_SZ_mem_MahlerZ_iff
-- name    : SZ.mem_MahlerZ_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:41:11.768149+00:00
-- url     : https://prove2.me/theorems/00644889-e9f3-420a-85f9-d1e9cdf84345
-- title:
--   SZ: mem Mahler Z iff
-- statement:
--   The SZ construction uses the mem Mahler Z iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Defs.lean#L69-L70
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Defs.lean#L69-L70

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

theorem SZ.mem_MahlerZ_iff {α : ℝ} :
    α ∈ MahlerZ ↔ 1 < α ∧ ∃ ξ : ℝ, ξ ≠ 0 ∧ ∀ n : ℕ, 1 ≤ n → Even ⌊ξ * α ^ n⌋ := by sorry
