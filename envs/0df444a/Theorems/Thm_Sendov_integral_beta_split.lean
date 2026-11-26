-- Prove2me | Theorems.Thm_Sendov_integral_beta_split
-- name    : Sendov.integral_beta_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:46:37.920776+00:00
-- url     : https://prove2.me/theorems/bc4a9c0a-92cd-4dc2-9484-e3ed33b73bcb
-- title:
--   Sendov: integral beta split
-- statement:
--   The integral form of the split, with the chord piece evaluated by the Beta integral.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Simplified.lean#L112-L171
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Simplified.lean#L112-L171

import Definitions.Def_Sendov_Reduction_Stat
import Definitions.Def_Sendov_Reduction_Simplified
set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {a x t α : ℝ}

theorem Sendov.integral_beta_split (hn : 5 ≤ n) (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (hax : 0 < a * x) :
    (∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2))
      ≤ 1 / ((a * x) ^ 2 * (((n : ℝ) - 1) * (n : ℝ)))
        + ((n : ℝ) - 2) / 2 * (a ^ 2 * (1 - x ^ 2))
          * ∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2) := by sorry
