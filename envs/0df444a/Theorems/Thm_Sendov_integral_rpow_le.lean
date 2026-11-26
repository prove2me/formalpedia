-- Prove2me | Theorems.Thm_Sendov_integral_rpow_le
-- name    : Sendov.integral_rpow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:56:21.272586+00:00
-- url     : https://prove2.me/theorems/e642a277-80e0-4155-8a09-9f3164ea577b
-- title:
--   Sendov: integral rpow le
-- statement:
--   **The odd-degree bound.**  The square root is eliminated in favour of polynomial
--   moments, at the cost of a free parameter `w > 0`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/OddBound.lean#L59-L71
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/OddBound.lean#L59-L71

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_FiniteRange_OddBound
set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {α q w : ℝ}

theorem Sendov.integral_rpow_le (hfeas : c n α ^ 2 ≤ A n α) (k : ℕ)
    (hk : ((n : ℝ) - 4) / 2 = (k : ℝ) + 1 / 2) (hw : 0 < w) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2))
      ≤ ∫ t in (0 : ℝ)..1, t ^ 3 * (Q n α t ^ k * (Q n α t / (2 * w) + w / 2)) := by sorry
