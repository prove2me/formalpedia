-- Prove2me | Theorems.Thm_Sendov_stat_of_one_le
-- name    : Sendov.stat_of_one_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T19:01:01.107882+00:00
-- url     : https://prove2.me/theorems/f88d2921-4473-4285-9cf9-4b05b4780597
-- title:
--   Sendov: stat of one le
-- statement:
--   **`(1le) + (beta-bound) ⟹ stat`.**
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Stat.lean#L69-L135
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Stat.lean#L69-L135

import Definitions.Def_Sendov_Reduction_BetaBound
import Definitions.Def_Sendov_Reduction_Stat
set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {a x α : ℝ}

theorem Sendov.stat_of_one_le (hn : 5 ≤ n) (hx : x ^ 2 ≤ 1)
    (hα : α = M n * (1 - a ^ 2) / 2) (hα0 : 0 < α)
    (hbeta : QQ (a * x) (a ^ 2) 1 ≤ α / (3 + α))
    (h1le : 1 ≤ QQ (a * x) (a ^ 2) 1 / (2 * α * (1 - QQ (a * x) (a ^ 2) 1))
      + QQ (a * x) (a ^ 2) 1 / (4 * α)
      + 1 / (2 * M n)
      + QQ (a * x) (a ^ 2) 1 / (4 * α * M n)
      + (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * QQ (a * x) (a ^ 2) 1 / (4 * α)
        * ∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2)) :
    1 ≤ R n α := by sorry
