-- Prove2me | Theorems.Thm_Sendov_norm_le_lowX
-- name    : Sendov.norm_le_lowX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:58:04.568862+00:00
-- url     : https://prove2.me/theorems/8d74201f-7461-5f59-b111-81616cdb4756
-- title:
--   Sendov: norm le low X
-- statement:
--   The Sendov construction uses the norm le low X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/LowDegree.lean#L59-L69
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/LowDegree.lean#L59-L69

import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_LowDegree
set_option autoImplicit false
open Sendov

theorem Sendov.norm_le_lowX {a t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ht0 : 0 ≤ t) {v : ℂ}
    (hv : ‖v‖ ≤ 1) : ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖ ≤ lowX a t := by sorry
