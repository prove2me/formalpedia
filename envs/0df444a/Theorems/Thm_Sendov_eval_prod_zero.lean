-- Prove2me | Theorems.Thm_Sendov_eval_prod_zero
-- name    : Sendov.eval_prod_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:51:47.225005+00:00
-- url     : https://prove2.me/theorems/63754a4b-9d6a-43ba-bb13-644b86848ef6
-- title:
--   Sendov: eval prod zero
-- statement:
--   `∏ⱼ (X - zⱼ)` at the origin.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Counterexample/Identities.lean#L125-L131
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Counterexample/Identities.lean#L125-L131

import Definitions.Def_Sendov_Counterexample_Factor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Sendov_Counterexample_Identities
set_option autoImplicit false
open Sendov
open Polynomial Multiset
variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ} {p : ℂ[X]}

theorem Sendov.eval_prod_zero (z : Multiset ℂ) :
    ((z.map (fun w => X - C w)).prod).eval 0 = (-1) ^ (Multiset.card z) * z.prod := by sorry
