-- Prove2me | Theorems.Thm_Sendov_prod_inv_sub_mul
-- name    : Sendov.prod_inv_sub_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:52:06.566274+00:00
-- url     : https://prove2.me/theorems/9dbb04ab-9931-47ce-b114-9ab787e2a7e5
-- title:
--   Sendov: prod inv sub mul
-- statement:
--   `∏ⱼ (1/vⱼ - a) · ∏ⱼ vⱼ = ∏ⱼ (1 - a vⱼ)`: clearing the denominators of the `q`-side.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Counterexample/Identities.lean#L149-L160
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Counterexample/Identities.lean#L149-L160

import Definitions.Def_Sendov_Counterexample_Factor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Sendov_Counterexample_Identities
set_option autoImplicit false
open Sendov
open Polynomial Multiset
variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ} {p : ℂ[X]}

theorem Sendov.prod_inv_sub_mul : ∀ (q : Multiset ℂ), (∀ v ∈ q, v ≠ 0) →
    (q.map (fun v => v⁻¹ - a)).prod * q.prod = (q.map (fun v => 1 - a * v)).prod := by sorry
