-- Prove2me | Theorems.Thm_Sendov_beta_split
-- name    : Sendov.beta_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:46:31.063298+00:00
-- url     : https://prove2.me/theorems/23c24df7-2a12-5084-8503-66246d94c755
-- title:
--   Sendov: beta split
-- statement:
--   The pointwise step: `β^((n-2)/2)` split into a chord power and a `β^((n-4)/2)` remainder.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Simplified.lean#L80-L109
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Simplified.lean#L80-L109

import Definitions.Def_Sendov_Reduction_Stat
import Definitions.Def_Sendov_Reduction_Simplified
set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {a x t α : ℝ}

theorem Sendov.beta_split (hn : 5 ≤ n) (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)
      ≤ (1 - a * x * t) ^ ((n : ℝ) - 2)
        + ((n : ℝ) - 2) / 2 * (a ^ 2 * t ^ 2 * (1 - x ^ 2))
          * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2) := by sorry
