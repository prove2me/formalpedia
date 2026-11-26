-- Prove2me | Theorems.Thm_Sendov_integral_anti
-- name    : Sendov.integral_anti
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:55:56.135131+00:00
-- url     : https://prove2.me/theorems/3fce3a15-7ef8-54e0-8788-be1111a47883
-- title:
--   Sendov: integral anti
-- statement:
--   The moment decreases with the degree: `Q` falls and the exponent rises.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Batch.lean#L105-L130
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Batch.lean#L105-L130

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_FiniteRange_Batch
set_option autoImplicit false
open Sendov
variable {α t : ℝ}
open MeasureTheory

theorem Sendov.integral_anti {m n : ℕ} (hm : 5 ≤ m) (h : m ≤ n) (hα : 0 ≤ α)
    (hcm : 0 ≤ c m α) (hfn : c n α ^ 2 ≤ A n α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2))
      ≤ ∫ t in (0 : ℝ)..1, t ^ 3 * Q m α t ^ (((m : ℝ) - 4) / 2) := by sorry
