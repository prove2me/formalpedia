-- Prove2me | Theorems.Thm_Sendov_one_sub_mul_pos
-- name    : Sendov.one_sub_mul_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:46:54.357908+00:00
-- url     : https://prove2.me/theorems/d127c3df-f987-41db-b149-d9825ee70e88
-- title:
--   Sendov: one sub mul pos
-- statement:
--   `ax t < 1` on `[0,1]`, so the chord `1 - axt` is positive.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Simplified.lean#L70-L77
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Simplified.lean#L70-L77

import Definitions.Def_Sendov_Reduction_Stat
import Definitions.Def_Sendov_Reduction_Simplified
set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {a x t α : ℝ}

theorem Sendov.one_sub_mul_pos (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 < 1 - a * x * t := by sorry
