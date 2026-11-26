-- Prove2me | Theorems.Thm_Sendov_eval_deriv_prod_zero
-- name    : Sendov.eval_deriv_prod_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:52:40.66619+00:00
-- url     : https://prove2.me/theorems/083614dd-b5ba-4ec1-a825-bc173e4f3782
-- title:
--   Sendov: eval deriv prod zero
-- statement:
--   The derivative of `∏ⱼ (X - zⱼ)` at the origin.  Proved by induction rather than through
--   `Polynomial.derivative_prod`, which would need the evaluation of a multiset sum.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Counterexample/Identities.lean#L135-L146
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Counterexample/Identities.lean#L135-L146

import Definitions.Def_Sendov_Counterexample_Factor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Sendov_Counterexample_Identities
set_option autoImplicit false
open Sendov
open Polynomial Multiset
variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ} {p : ℂ[X]}

theorem Sendov.eval_deriv_prod_zero : ∀ (z : Multiset ℂ),
    (derivative (z.map (fun w => X - C w)).prod).eval 0
      = -((-1) ^ (Multiset.card z) * sumEraseProd z) := by sorry
