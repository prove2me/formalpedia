-- Prove2me | Theorems.Thm_Sendov_pev_append_zeros
-- name    : Sendov.pev_append_zeros
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:04:47.332119+00:00
-- url     : https://prove2.me/theorems/f8d22908-85ab-47c3-b5f0-3f54221689ef
-- title:
--   Sendov: pev append zeros
-- statement:
--   Evaluation ignores trailing zeros.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L319-L326
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L319-L326

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
open Sendov

theorem Sendov.pev_append_zeros (p : List ℤ) (j : ℕ) (α : ℝ) :
    pev (p ++ List.replicate j 0) α = pev p α := by sorry
