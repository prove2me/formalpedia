-- Prove2me | Theorems.Thm_Sendov_c_le_mul
-- name    : Sendov.c_le_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:45:26.325882+00:00
-- url     : https://prove2.me/theorems/d3cbaf9a-05be-40d2-8746-ac40ad33b6ba
-- title:
--   Sendov: c le mul
-- statement:
--   Under `(beta-bound)`, `Sendov.c n α ≤ ax`: the substitution only ever lowers `ax`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Stat.lean#L48-L55
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Stat.lean#L48-L55

import Definitions.Def_Sendov_Reduction_BetaBound
import Definitions.Def_Sendov_Reduction_Stat
set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {a x α : ℝ}

theorem Sendov.c_le_mul (hn : 2 ≤ n) (hα : α = M n * (1 - a ^ 2) / 2) (hα0 : 0 < α)
    (hbeta : QQ (a * x) (a ^ 2) 1 ≤ α / (3 + α)) : c n α ≤ a * x := by sorry
