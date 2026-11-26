-- Prove2me | Theorems.Thm_Sendov_alpha_le_seventeen
-- name    : Sendov.alpha_le_seventeen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T19:01:33.319548+00:00
-- url     : https://prove2.me/theorems/b6a24844-1e6b-4ce0-ba14-7e6e6135f4d4
-- title:
--   Sendov: alpha le seventeen
-- statement:
--   **`(beta-bound) + (origin-exact) ⟹ α ≤ 17`.**
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Alpha17.lean#L106-L277
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Alpha17.lean#L106-L277

import Definitions.Def_Sendov_Reduction_Simplified
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_Sendov_Reduction_Alpha17
set_option autoImplicit false
open Sendov
open MeasureTheory Real
set_option maxHeartbeats 1000000

theorem Sendov.alpha_le_seventeen {n : ℕ} {a x α : ℝ} (hn : 5 ≤ n)
    (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (hα : α = M n * (1 - a ^ 2) / 2)
    (hbeta : QQ (a * x) (a ^ 2) 1 ≤ α / (3 + α))
    (hlogb : Real.log α ≤ α * (1 - QQ (a * x) (a ^ 2) 1))
    (horigin : 2 * α + a * x ≤ (1 - x ^ 2) / (2 * M n)
      + a ^ 2 * n * M n * ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) :
    α ≤ 17 := by sorry
