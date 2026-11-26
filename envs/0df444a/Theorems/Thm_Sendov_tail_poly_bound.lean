-- Prove2me | Theorems.Thm_Sendov_tail_poly_bound
-- name    : Sendov.tail_poly_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:50:10.606842+00:00
-- url     : https://prove2.me/theorems/6479a059-3e7a-5b3c-94cb-b874e3d963a4
-- title:
--   Sendov: tail poly bound
-- statement:
--   The polynomial bound behind the geometric term: `v(2v + 2 + 1/17) e^{-2.83 v} ≤ 0.4118`
--   for `v ≥ 0`.  Four terms of the exponential series suffice; the true maximum is `0.3722`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Alpha17.lean#L89-L97
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Alpha17.lean#L89-L97

import Definitions.Def_Sendov_Reduction_Simplified
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_Sendov_Reduction_Alpha17
set_option autoImplicit false
open Sendov
open MeasureTheory Real

theorem Sendov.tail_poly_bound {v : ℝ} (hv : 0 ≤ v) :
    v * (2 * (v + 1) + 1 / 17) * exp (-(2.83 * v)) ≤ 0.4118 := by sorry
