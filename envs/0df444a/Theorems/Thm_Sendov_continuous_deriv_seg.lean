-- Prove2me | Theorems.Thm_Sendov_continuous_deriv_seg
-- name    : Sendov.continuous_deriv_seg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:52:47.059566+00:00
-- url     : https://prove2.me/theorems/d5768d7c-d2ea-425d-aae2-189d9a6ea7e9
-- title:
--   Sendov: continuous deriv seg
-- statement:
--   The integrand of the representation below is continuous.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Counterexample/Identities.lean#L203-L205
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Counterexample/Identities.lean#L203-L205

import Definitions.Def_Sendov_Counterexample_Factor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Sendov_Counterexample_Identities
set_option autoImplicit false
open Sendov
open Polynomial Multiset
variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ} {p : ℂ[X]}
open MeasureTheory

theorem Sendov.continuous_deriv_seg (p : ℂ[X]) (a w : ℂ) :
    Continuous fun t : ℝ => (derivative p).eval (a + (t : ℂ) * (w - a)) := by sorry
