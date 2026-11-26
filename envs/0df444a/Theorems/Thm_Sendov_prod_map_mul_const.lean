-- Prove2me | Theorems.Thm_Sendov_prod_map_mul_const
-- name    : Sendov.prod_map_mul_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:52:46.466665+00:00
-- url     : https://prove2.me/theorems/e22bcd6a-07a9-5bf2-9df8-09f056f467a7
-- title:
--   Sendov: prod map mul const
-- statement:
--   Pulling a constant out of a product over a multiset.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Counterexample/Identities.lean#L297-L303
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Counterexample/Identities.lean#L297-L303

import Definitions.Def_Sendov_Counterexample_Factor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Sendov_Counterexample_Identities
set_option autoImplicit false
open Sendov
open Polynomial Multiset
variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ} {p : ℂ[X]}

theorem Sendov.prod_map_mul_const (b : ℂ) (s : Multiset ℂ) (f : ℂ → ℂ) :
    (s.map (fun v => b * f v)).prod = b ^ (Multiset.card s) * (s.map f).prod := by sorry
