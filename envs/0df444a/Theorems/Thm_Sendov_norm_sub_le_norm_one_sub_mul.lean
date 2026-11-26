-- Prove2me | Theorems.Thm_Sendov_norm_sub_le_norm_one_sub_mul
-- name    : Sendov.norm_sub_le_norm_one_sub_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:53:07.159446+00:00
-- url     : https://prove2.me/theorems/95cb061f-4e4c-579d-9dab-23934700ed97
-- title:
--   Sendov: norm sub le norm one sub mul
-- statement:
--   `|a - z| ≤ |1 - a z|` for real `a` with `|a| ≤ 1` and `z` in the closed unit disk.  The
--   difference of squares is `(1-a²)(1-|z|²)`, which is why `a` must be real: for complex `a` the
--   cross terms contribute `(conj a - a)(z - conj z)`, which need not vanish.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Polar.lean#L50-L71
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Polar.lean#L50-L71

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_Polar
set_option autoImplicit false
open Sendov
open Polynomial MeasureTheory

theorem Sendov.norm_sub_le_norm_one_sub_mul {a : ℝ} (ha : |a| ≤ 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖(a : ℂ) - z‖ ≤ ‖1 - (a : ℂ) * z‖ := by sorry
