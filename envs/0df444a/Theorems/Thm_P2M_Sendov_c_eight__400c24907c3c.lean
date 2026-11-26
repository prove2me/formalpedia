-- Prove2me | Theorems.Thm_P2M_Sendov_c_eight__400c24907c3c
-- name    : P2M_Sendov_c_eight__400c24907c3c
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:59:56.017649+00:00
-- url     : https://prove2.me/theorems/363e4a13-76fe-427d-ac43-22a05bd666a7
-- title:
--   P2 M Sendov c eight  400c24907c3c: P2 M Sendov c eight  400c24907c3c
-- statement:
--   The P2 M Sendov c eight  400c24907c3c construction uses the P2 M Sendov c eight  400c24907c3c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree8.lean#L44-L48
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree8.lean#L44-L48

import Definitions.Def_Sendov_FiniteRange_Reduce
import Definitions.Def_Sendov_FiniteRange_Degree8
set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}

theorem P2M_Sendov_c_eight__400c24907c3c (hα : 0 ≤ α) : c 8 α = (42 + α - 2 * α ^ 2) / (14 * (3 + α)) := by sorry

alias «Sendov».«c_eight'» := P2M_Sendov_c_eight__400c24907c3c
