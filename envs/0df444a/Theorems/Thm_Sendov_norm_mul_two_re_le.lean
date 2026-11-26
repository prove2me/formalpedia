-- Prove2me | Theorems.Thm_Sendov_norm_mul_two_re_le
-- name    : Sendov.norm_mul_two_re_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:57:30.204247+00:00
-- url     : https://prove2.me/theorems/5fd0c940-daac-5a00-add8-ca46c1f144fe
-- title:
--   Sendov: norm mul two re le
-- statement:
--   `|s + it| ≤ s + t²/(2s)` for `s > 0`, in cleared form.  Squaring both sides leaves
--   `t⁴ ≥ 0`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/OriginExact.lean#L58-L63
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/OriginExact.lean#L58-L63

import Definitions.Def_Sendov_Analytic_Origin
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_OriginExact
set_option autoImplicit false
open Sendov
open Complex (I)

theorem Sendov.norm_mul_two_re_le {w : ℂ} (_hs : 0 < w.re) :
    ‖w‖ * (2 * w.re) ≤ 2 * w.re ^ 2 + w.im ^ 2 := by sorry
