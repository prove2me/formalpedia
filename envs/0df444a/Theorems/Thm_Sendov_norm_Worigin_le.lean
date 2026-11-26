-- Prove2me | Theorems.Thm_Sendov_norm_Worigin_le
-- name    : Sendov.norm_Worigin_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:57:59.874459+00:00
-- url     : https://prove2.me/theorems/21e96b47-c3d7-498a-8d23-c448b338256f
-- title:
--   Sendov: norm Worigin le
-- statement:
--   Eliminating `y`: `‖W‖ ≤ Re W + (Im W)²/(2 Re W)`, then `Re W ≥ a²(n-1)` and `y² ≤ 1 - x²`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/OriginExact.lean#L117-L138
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/OriginExact.lean#L117-L138

import Definitions.Def_Sendov_Analytic_Origin
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_OriginExact
set_option autoImplicit false
open Sendov
open Complex (I)

theorem Sendov.norm_Worigin_le {n : ℕ} {a x y : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hn1 : (0 : ℝ) < (n : ℝ) - 1) (hxle : x ≤ 1) (hy2 : y ^ 2 ≤ 1 - x ^ 2) :
    ‖Worigin n a x y‖
      ≤ a ^ 2 * ((n : ℝ) - 1) + 1 - a * x + (1 - x ^ 2) / (2 * ((n : ℝ) - 1)) := by sorry
