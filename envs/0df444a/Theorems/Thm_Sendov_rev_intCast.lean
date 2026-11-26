-- Prove2me | Theorems.Thm_Sendov_rev_intCast
-- name    : Sendov.rev_intCast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:03:53.169787+00:00
-- url     : https://prove2.me/theorems/7d65e5fd-385e-40d7-9a37-523d7502fe19
-- title:
--   Sendov: rev int Cast
-- statement:
--   Evaluating a row over `ℝ` at integer points is the packed evaluation over `ℤ`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L59-L66
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L59-L66

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
open Sendov

theorem Sendov.rev_intCast (r : List (List ℤ)) (β τ : ℤ) :
    rev r (β : ℝ) (τ : ℝ) = (pevZ (rowZ r β) τ : ℝ) := by sorry
