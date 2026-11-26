-- Prove2me | Theorems.Thm_Sendov_first_origin_identity
-- name    : Sendov.first_origin_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T19:02:49.897725+00:00
-- url     : https://prove2.me/theorems/710a9bb8-5b88-5644-a9c0-30c21b15a50b
-- title:
--   Sendov: first origin identity
-- statement:
--   **The first origin identity**, division-free.  The blog post's
--   `(-1)^{n-1} ∏ zⱼ = (n / ∏ qⱼ) ∫₀¹ F(t) dt` with the denominator cleared, where
--   `F(t) = ∏ⱼ (1 - a t qⱼ)`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Counterexample/Identities.lean#L241-L292
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Counterexample/Identities.lean#L241-L292

import Definitions.Def_Sendov_Counterexample_Factor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Sendov_Counterexample_Identities
set_option autoImplicit false
open Sendov
open Polynomial Multiset
variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ} {p : ℂ[X]}
open MeasureTheory

theorem Sendov.first_origin_identity {p : ℂ[X]} (hc0 : c ≠ 0) (ha0 : a ≠ 0)
    (hzcard : z.card = n - 1) (hq0 : ∀ v ∈ q, v ≠ 0) (hpa : p.eval a = 0)
    (hpz : p = C c * ((X - C a) * (z.map (fun w => X - C w)).prod))
    (hpq : derivative p
      = C ((n : ℂ) * c) * ((q.map (fun v => a - v⁻¹)).map (fun w => X - C w)).prod) :
    (n : ℂ) * ∫ t in (0 : ℝ)..1, (q.map (fun v => 1 - a * (t : ℂ) * v)).prod
      = (-1) ^ (n - 1) * q.prod * z.prod := by sorry
