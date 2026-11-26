-- Prove2me | Theorems.Thm_Sendov_lowJ_four_lt_one
-- name    : Sendov.lowJ_four_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:58:26.520863+00:00
-- url     : https://prove2.me/theorems/e7e2619f-05ad-4949-8aca-01eab964e7b5
-- title:
--   Sendov: low J four lt one
-- statement:
--   The Sendov construction uses the low J four lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/LowDegree.lean#L157-L162
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/LowDegree.lean#L157-L162

import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_LowDegree
set_option autoImplicit false
open Sendov

theorem Sendov.lowJ_four_lt_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : lowJ 4 a < 1 := by sorry
