-- Prove2me | Theorems.Thm_Sendov_centroid_identity
-- name    : Sendov.centroid_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T19:02:32.829685+00:00
-- url     : https://prove2.me/theorems/6f4ea100-69a4-4e6c-92d0-f4526cb32211
-- title:
--   Sendov: centroid identity
-- statement:
--   **The centroid identity.**  `(n-1)(a + ∑ zⱼ) = n ∑ⱼ (a - 1/qⱼ)`: the centroid of the
--   zeroes equals the centroid of the critical points.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Counterexample/Identities.lean#L60-L98
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Counterexample/Identities.lean#L60-L98

import Definitions.Def_Sendov_Counterexample_Factor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Sendov_Counterexample_Identities
set_option autoImplicit false
open Sendov
open Polynomial Multiset
variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ} {p : ℂ[X]}

theorem Sendov.centroid_identity (hn : 2 ≤ n) {p : ℂ[X]} (hc0 : c ≠ 0)
    (hzcard : z.card = n - 1) (hqcard : q.card = n - 1)
    (hpz : p = C c * ((X - C a) * (z.map (fun w => X - C w)).prod))
    (hpq : derivative p
      = C ((n : ℂ) * c) * ((q.map (fun v => a - v⁻¹)).map (fun w => X - C w)).prod) :
    ((n : ℂ) - 1) * (a + z.sum) = (n : ℂ) * (q.map (fun v => a - v⁻¹)).sum := by sorry
