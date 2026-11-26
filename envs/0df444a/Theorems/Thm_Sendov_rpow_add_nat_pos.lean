-- Prove2me | Theorems.Thm_Sendov_rpow_add_nat_pos
-- name    : Sendov.rpow_add_nat_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:55:15.351054+00:00
-- url     : https://prove2.me/theorems/5fb6e9ae-6f56-4813-9757-8ba23de045de
-- title:
--   Sendov: rpow add nat pos
-- statement:
--   `x ^ (s + m) = x ^ s * x ^ m` for positive `x` and a natural `m`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Rpow.lean#L38-L40
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Rpow.lean#L38-L40

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_Common_Rpow
set_option autoImplicit false
open Sendov
open MeasureTheory

theorem Sendov.rpow_add_nat_pos {x : ℝ} (hx : 0 < x) (s : ℝ) (m : ℕ) :
    x ^ (s + (m : ℝ)) = x ^ s * x ^ m := by sorry
