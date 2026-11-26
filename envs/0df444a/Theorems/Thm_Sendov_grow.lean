-- Prove2me | Theorems.Thm_Sendov_grow
-- name    : Sendov.grow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:57:45.651183+00:00
-- url     : https://prove2.me/theorems/d85ddcb5-3260-5053-86f4-9f29c82f65ee
-- title:
--   Sendov: grow
-- statement:
--   **(grow).**  `‖W‖ ≥ 2an/(n-1)`.  Bounding `‖W‖` below by its real part reduces this to
--   `(n-1)²a² - (3n-1)a + (n-1) > 0`; completing the square turns that into
--   `4(n-1)³ - (3n-1)² > 0`, which is exactly where `n ≥ 5` is needed.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/OriginExact.lean#L92-L105
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/OriginExact.lean#L92-L105

import Definitions.Def_Sendov_Analytic_Origin
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_OriginExact
set_option autoImplicit false
open Sendov
open Complex (I)

theorem Sendov.grow {n : ℕ} (hn : 5 ≤ n) {a x y : ℝ} (ha0 : 0 < a) (hx : x ≤ 1) :
    2 * a * (n : ℝ) / ((n : ℝ) - 1) ≤ ‖Worigin n a x y‖ := by sorry
