-- Prove2me | Theorems.Thm_Sendov_lowJ_four
-- name    : Sendov.lowJ_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:58:10.358681+00:00
-- url     : https://prove2.me/theorems/2547c4ac-f8dc-5c79-aa20-a29405107e0a
-- title:
--   Sendov: low J four
-- statement:
--   `J₄(a)`, by the fundamental theorem of calculus against an explicit antiderivative.  The
--   antiderivative is written without dividing by `1 - a²`, so no side condition on `a` appears.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/LowDegree.lean#L111-L141
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/LowDegree.lean#L111-L141

import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_LowDegree
set_option autoImplicit false
open Sendov

theorem Sendov.lowJ_four (a : ℝ) :
    lowJ 4 a = a ^ 4 + 2 * a ^ 3 * (1 - a ^ 2) + 2 * a ^ 2 * (1 - a ^ 2) ^ 2
      + a * (1 - a ^ 2) ^ 3 + (1 - a ^ 2) ^ 4 / 5 := by sorry
