-- Prove2me | Theorems.Thm_Sendov_Worigin_re
-- name    : Sendov.Worigin_re
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:56:33.900639+00:00
-- url     : https://prove2.me/theorems/53efe54c-77c1-5608-9c8b-3e2c73447df4
-- title:
--   Sendov: Worigin re
-- statement:
--   The Sendov construction uses the Worigin re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/OriginExact.lean#L78-L82
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/OriginExact.lean#L78-L82

import Definitions.Def_Sendov_Analytic_Origin
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_OriginExact
set_option autoImplicit false
open Sendov
open Complex (I)

theorem Sendov.Worigin_re (n : ℕ) (a x y : ℝ) :
    (Worigin n a x y).re = a ^ 2 * ((n : ℝ) - 1) + 1 - a * x := by sorry
