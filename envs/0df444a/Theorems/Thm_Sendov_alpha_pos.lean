-- Prove2me | Theorems.Thm_Sendov_alpha_pos
-- name    : Sendov.alpha_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:59:47.633699+00:00
-- url     : https://prove2.me/theorems/8beb5286-6c6a-586d-808e-1fcec7384a49
-- title:
--   Sendov: alpha pos
-- statement:
--   The Sendov construction uses the alpha pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Setup.lean#L64-L69
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Setup.lean#L64-L69

import Definitions.Def_Sendov_Common_Chord
import Definitions.Def_Sendov_Reduction_Setup
set_option autoImplicit false
open Sendov
variable {n : ℕ} {a x t α : ℝ}

theorem Sendov.alpha_pos (hn : 2 ≤ n) (ha1 : a < 1) (_ha0 : 0 ≤ a)
    (hα : α = M n * (1 - a ^ 2) / 2) : 0 < α := by sorry
