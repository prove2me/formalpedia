-- Prove2me | Theorems.Thm_Sendov_prod_inv_mul
-- name    : Sendov.prod_inv_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:52:56.160962+00:00
-- url     : https://prove2.me/theorems/cc37e96d-2d29-4244-b170-b86e069d5a52
-- title:
--   Sendov: prod inv mul
-- statement:
--   `∏ⱼ (1/vⱼ) · ∏ⱼ vⱼ = 1`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Counterexample/Identities.lean#L306-L317
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Counterexample/Identities.lean#L306-L317

import Definitions.Def_Sendov_Counterexample_Factor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Sendov_Counterexample_Identities
set_option autoImplicit false
open Sendov
open Polynomial Multiset
variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ} {p : ℂ[X]}

theorem Sendov.prod_inv_mul : ∀ (q : Multiset ℂ), (∀ v ∈ q, v ≠ 0) →
    (q.map (fun v => v⁻¹)).prod * q.prod = 1 := by sorry
