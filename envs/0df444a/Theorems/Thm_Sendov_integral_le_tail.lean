-- Prove2me | Theorems.Thm_Sendov_integral_le_tail
-- name    : Sendov.integral_le_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:08:02.70191+00:00
-- url     : https://prove2.me/theorems/d364797a-adbe-4d53-8eaa-9736754807f3
-- title:
--   Sendov: integral le tail
-- statement:
--   **The tail bound**, read off from `Sendov.integral_le_tail_cube`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Tail.lean#L45-L52
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Tail.lean#L45-L52

import Definitions.Def_Sendov_Common_Chord
import Definitions.Def_Sendov_LargeDegree_Tail
set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {α t : ℝ}

theorem Sendov.integral_le_tail (hn : 2 ≤ n) (hα : 0 ≤ α) (hfeas : c n α ^ 2 ≤ A n α)
    (hc : 0 < c n α) {r : ℝ} (hr : 0 < r) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ r)
      ≤ 6 / (c n α ^ 4 * ((r + 1) * (r + 2) * (r + 3) * (r + 4)))
        + (α / (3 + α)) ^ r / 4 := by sorry
