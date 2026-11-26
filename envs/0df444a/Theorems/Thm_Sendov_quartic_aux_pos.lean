-- Prove2me | Theorems.Thm_Sendov_quartic_aux_pos
-- name    : Sendov.quartic_aux_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:58:33.171614+00:00
-- url     : https://prove2.me/theorems/4c94fa13-680c-43cd-b050-62e79b557b10
-- title:
--   Sendov: quartic aux pos
-- statement:
--   The Sendov construction uses the quartic aux pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/LowDegree.lean#L148-L155
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/LowDegree.lean#L148-L155

import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_LowDegree
set_option autoImplicit false
open Sendov

theorem Sendov.quartic_aux_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    0 < a ^ 4 - 3 * a ^ 3 + 3 * a + 4 := by sorry
