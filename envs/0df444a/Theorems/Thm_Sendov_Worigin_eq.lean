-- Prove2me | Theorems.Thm_Sendov_Worigin_eq
-- name    : Sendov.Worigin_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:56:32.233072+00:00
-- url     : https://prove2.me/theorems/f3a704b4-1a98-5460-a63a-4ea24e688591
-- title:
--   Sendov: Worigin eq
-- statement:
--   The Sendov construction uses the Worigin eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/OriginExact.lean#L71-L76
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/OriginExact.lean#L71-L76

import Definitions.Def_Sendov_Analytic_Origin
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_OriginExact
set_option autoImplicit false
open Sendov
open Complex (I)

theorem Sendov.Worigin_eq (n : ℕ) (a x y : ℝ) :
    Worigin n a x y = ((a ^ 2 * ((n : ℝ) - 1) + 1 - a * x : ℝ) : ℂ)
      + ((-(a * y) : ℝ) : ℂ) * I := by sorry
