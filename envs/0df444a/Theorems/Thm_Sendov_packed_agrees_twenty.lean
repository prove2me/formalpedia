-- Prove2me | Theorems.Thm_Sendov_packed_agrees_twenty
-- name    : Sendov.packed_agrees_twenty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:19:10.213827+00:00
-- url     : https://prove2.me/theorems/bcf05612-bd49-4d15-a852-d26e8799165a
-- title:
--   Sendov: packed agrees twenty
-- statement:
--   **The cross-check.**  The multinomial formula and the packed recurrence agree.  Neither
--   side is expanded: both compute the same integral, so they are equal by transitivity.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree20Packed.lean#L59-L61
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree20Packed.lean#L59-L61

import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Reduce
import Definitions.Def_Sendov_FiniteRange_Degree20Packed
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 100000
open Sendov

theorem Sendov.packed_agrees_twenty (α : ℝ) (hα : 0 ≤ α) :
    pev Nmom20 α / ((L20 : ℝ) * (2 * M 20 * (3 + α)) ^ 8) = mom 20 α 8 := by sorry
