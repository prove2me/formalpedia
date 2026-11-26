-- Prove2me | Theorems.Thm_Sendov_lowX_nonneg
-- name    : Sendov.lowX_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:55:36.374212+00:00
-- url     : https://prove2.me/theorems/e0b4340c-6f4a-4cbc-b7e9-705caf7ed664
-- title:
--   Sendov: low X nonneg
-- statement:
--   The Sendov construction uses the low X nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/LowDegree.lean#L48-L51
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/LowDegree.lean#L48-L51

import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_LowDegree
set_option autoImplicit false
open Sendov

theorem Sendov.lowX_nonneg {a t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ht0 : 0 ≤ t) : 0 ≤ lowX a t := by sorry
