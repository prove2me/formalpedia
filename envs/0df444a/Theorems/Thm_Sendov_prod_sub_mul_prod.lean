-- Prove2me | Theorems.Thm_Sendov_prod_sub_mul_prod
-- name    : Sendov.prod_sub_mul_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T19:02:58.571699+00:00
-- url     : https://prove2.me/theorems/500347b1-d80b-5302-88f4-a339ce59c88f
-- title:
--   Sendov: prod sub mul prod
-- statement:
--   **`p'(a)` two ways.**  `(∏ⱼ qⱼ) ∏ⱼ (a - zⱼ) = n`.  This is what makes the polar identity
--   usable without dividing: it is the denominator of the blog post's
--   `∏ⱼ (1-azⱼ)/(a-zⱼ)`, expressed as a product.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Counterexample/Identities.lean#L322-L349
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Counterexample/Identities.lean#L322-L349

import Definitions.Def_Sendov_Counterexample_Factor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Sendov_Counterexample_Identities
set_option autoImplicit false
open Sendov
open Polynomial Multiset
variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ} {p : ℂ[X]}

theorem Sendov.prod_sub_mul_prod (hc0 : c ≠ 0) (hq0 : ∀ v ∈ q, v ≠ 0)
    (hpz : p = C c * ((X - C a) * (z.map (fun w => X - C w)).prod))
    (hpq : derivative p
      = C ((n : ℂ) * c) * ((q.map (fun v => a - v⁻¹)).map (fun w => X - C w)).prod) :
    q.prod * (z.map (fun w => a - w)).prod = (n : ℂ) := by sorry
