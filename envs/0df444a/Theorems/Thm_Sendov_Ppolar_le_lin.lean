-- Prove2me | Theorems.Thm_Sendov_Ppolar_le_lin
-- name    : Sendov.Ppolar_le_lin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:43:18.23096+00:00
-- url     : https://prove2.me/theorems/588d0208-97c6-5acd-b2ee-e5f8003f37b7
-- title:
--   Sendov: Ppolar le lin
-- statement:
--   The pointwise bound `(at)`.  An identity apart from `t² ≤ t`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Polar.lean#L45-L50
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Polar.lean#L45-L50

import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Reduction_Polar
set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {a x t α : ℝ}

theorem Sendov.Ppolar_le_lin (a x : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Ppolar a x t ≤ 1 + (1 - a ^ 2) * (-1 + (2 - QQ (a * x) (a ^ 2) 1) * t) := by sorry
