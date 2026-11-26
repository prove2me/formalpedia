-- Prove2me | Theorems.Thm_Sendov_Ppolar_rpow_le
-- name    : Sendov.Ppolar_rpow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:43:15.560224+00:00
-- url     : https://prove2.me/theorems/a5185e28-5fa3-4147-a629-ae761082fc3a
-- title:
--   Sendov: Ppolar rpow le
-- statement:
--   The pointwise bound after raising to the power `(n-1)/2`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Polar.lean#L53-L71
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Polar.lean#L53-L71

import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Reduction_Polar
set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {a x t α : ℝ}

theorem Sendov.Ppolar_rpow_le (hn : 2 ≤ n) (hx : x ^ 2 ≤ 1) (hα : α = M n * (1 - a ^ 2) / 2)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Ppolar a x t ^ (((n : ℝ) - 1) / 2)
      ≤ Real.exp (α * (-1 + (2 - QQ (a * x) (a ^ 2) 1) * t)) := by sorry
