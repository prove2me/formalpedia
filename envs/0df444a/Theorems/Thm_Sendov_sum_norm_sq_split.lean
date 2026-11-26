-- Prove2me | Theorems.Thm_Sendov_sum_norm_sq_split
-- name    : Sendov.sum_norm_sq_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:53:30.535105+00:00
-- url     : https://prove2.me/theorems/5d1f0474-ea11-5993-84ea-c56a7dbbceef
-- title:
--   Sendov: sum norm sq split
-- statement:
--   Splitting `∑ⱼ ‖a + s qⱼ‖²` into its three pieces.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Polar.lean#L174-L184
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Polar.lean#L174-L184

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_Polar
set_option autoImplicit false
open Sendov
open Polynomial MeasureTheory

theorem Sendov.sum_norm_sq_split (a s : ℝ) (q : Multiset ℂ) :
    (q.map (fun v => ‖(a : ℂ) + (s : ℂ) * v‖ ^ 2)).sum
      = (q.card : ℝ) * a ^ 2 + 2 * a * s * ((q.map (fun v => v.re)).sum)
        + s ^ 2 * ((q.map (fun v => ‖v‖ ^ 2)).sum) := by sorry
