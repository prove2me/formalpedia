-- Prove2me | Theorems.Thm_Sendov_Worigin_im
-- name    : Sendov.Worigin_im
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:57:42.157855+00:00
-- url     : https://prove2.me/theorems/4807c9b0-7a65-58bb-a681-ce8a04503544
-- title:
--   Sendov: Worigin im
-- statement:
--   The Sendov construction uses the Worigin im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/OriginExact.lean#L84-L87
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/OriginExact.lean#L84-L87

import Definitions.Def_Sendov_Analytic_Origin
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_OriginExact
set_option autoImplicit false
open Sendov
open Complex (I)

theorem Sendov.Worigin_im (n : ℕ) (a x y : ℝ) : (Worigin n a x y).im = -(a * y) := by sorry
