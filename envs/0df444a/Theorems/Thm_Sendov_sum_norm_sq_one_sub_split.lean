-- Prove2me | Theorems.Thm_Sendov_sum_norm_sq_one_sub_split
-- name    : Sendov.sum_norm_sq_one_sub_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:55:49.318958+00:00
-- url     : https://prove2.me/theorems/d3205419-b4d8-467b-883e-a540aa5d03d0
-- title:
--   Sendov: sum norm sq one sub split
-- statement:
--   The Sendov construction uses the sum norm sq one sub split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Origin.lean#L97-L107
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Origin.lean#L97-L107

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Origin
set_option autoImplicit false
open Sendov

theorem Sendov.sum_norm_sq_one_sub_split (s : ℝ) (q : Multiset ℂ) :
    (q.map (fun v => ‖1 + (s : ℂ) * v‖ ^ 2)).sum
      = (q.card : ℝ) + 2 * s * ((q.map (fun v => v.re)).sum)
        + s ^ 2 * ((q.map (fun v => ‖v‖ ^ 2)).sum) := by sorry
