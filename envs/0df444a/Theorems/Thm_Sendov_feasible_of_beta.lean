-- Prove2me | Theorems.Thm_Sendov_feasible_of_beta
-- name    : Sendov.feasible_of_beta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T19:00:41.374873+00:00
-- url     : https://prove2.me/theorems/3b1f5594-77b9-5306-806a-dac93841e4ed
-- title:
--   Sendov: feasible of beta
-- statement:
--   `(beta-bound)` supplies the feasibility constraint `c² ≤ A` that `Sendov.stat_lt_one`
--   requires.  It is `c ≤ ax` squared, together with `x² ≤ 1`: the substitution can only lower
--   `ax`, and `ax` is already at most `a`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Stat.lean#L60-L66
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Stat.lean#L60-L66

import Definitions.Def_Sendov_Reduction_BetaBound
import Definitions.Def_Sendov_Reduction_Stat
set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {a x α : ℝ}

theorem Sendov.feasible_of_beta (hn : 2 ≤ n) (hx : x ^ 2 ≤ 1)
    (hα : α = M n * (1 - a ^ 2) / 2) (hα0 : 0 < α)
    (hbeta : QQ (a * x) (a ^ 2) 1 ≤ α / (3 + α)) : c n α ^ 2 ≤ A n α := by sorry
