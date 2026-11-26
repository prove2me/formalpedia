-- Prove2me | Theorems.Thm_Sendov_second_origin_identity
-- name    : Sendov.second_origin_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T19:02:37.544255+00:00
-- url     : https://prove2.me/theorems/b3e435ce-f064-4b10-ad2d-eb4fb8531612
-- title:
--   Sendov: second origin identity
-- statement:
--   **The second origin identity**, division-free.  The blog post's form
--   `(-1)^{n-1}(∏ zⱼ)(1 + a ∑ 1/zⱼ) = (n/∏ qⱼ) F(1)` after clearing both denominators.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Counterexample/Identities.lean#L165-L197
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Counterexample/Identities.lean#L165-L197

import Definitions.Def_Sendov_Counterexample_Factor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Sendov_Counterexample_Identities
set_option autoImplicit false
open Sendov
open Polynomial Multiset
variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ} {p : ℂ[X]}
open scoped Classical

theorem Sendov.second_origin_identity {p : ℂ[X]} (hc0 : c ≠ 0)
    (hzcard : z.card = n - 1) (hq0 : ∀ v ∈ q, v ≠ 0)
    (hpz : p = C c * ((X - C a) * (z.map (fun w => X - C w)).prod))
    (hpq : derivative p
      = C ((n : ℂ) * c) * ((q.map (fun v => a - v⁻¹)).map (fun w => X - C w)).prod) :
    (n : ℂ) * (q.map (fun v => 1 - a * v)).prod
      = (-1) ^ (n - 1) * q.prod * (z.prod + a * sumEraseProd z) := by sorry
