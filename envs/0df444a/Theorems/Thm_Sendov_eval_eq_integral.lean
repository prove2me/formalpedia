-- Prove2me | Theorems.Thm_Sendov_eval_eq_integral
-- name    : Sendov.eval_eq_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:52:05.833907+00:00
-- url     : https://prove2.me/theorems/c739b327-086e-5590-811b-f6cefe8c747f
-- title:
--   Sendov: eval eq integral
-- statement:
--   **The integral representation.**  `p(w) = (w-a) ∫₀¹ p'(a + t(w-a)) dt` when `a` is a root
--   of `p`.  This is the fundamental theorem of calculus along the segment from `a` to `w`,
--   parametrized by a real variable; it replaces the blog post's `p(z) = (z-a)∫₀¹ n ∏ⱼ (t(z-a) +
--   1/qⱼ) dt`, which is the same statement with `p'` already factored.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Counterexample/Identities.lean#L212-L233
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Counterexample/Identities.lean#L212-L233

import Definitions.Def_Sendov_Counterexample_Factor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Sendov_Counterexample_Identities
set_option autoImplicit false
open Sendov
open Polynomial Multiset
variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ} {p : ℂ[X]}
open MeasureTheory

theorem Sendov.eval_eq_integral {p : ℂ[X]} {a : ℂ} (hpa : p.eval a = 0) (w : ℂ) :
    p.eval w = (w - a) * ∫ t in (0 : ℝ)..1, (derivative p).eval (a + (t : ℂ) * (w - a)) := by sorry
