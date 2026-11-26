-- Prove2me | Theorems.Thm_Sendov_prod_map_neg
-- name    : Sendov.prod_map_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:52:46.701799+00:00
-- url     : https://prove2.me/theorems/fe76d0cc-24ef-4092-93e3-1fde3661cae5
-- title:
--   Sendov: prod map neg
-- statement:
--   Negating a multiset before taking the product.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Counterexample/Identities.lean#L116-L122
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Counterexample/Identities.lean#L116-L122

import Definitions.Def_Sendov_Counterexample_Factor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Sendov_Counterexample_Identities
set_option autoImplicit false
open Sendov
open Polynomial Multiset
variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ} {p : ℂ[X]}

theorem Sendov.prod_map_neg (s : Multiset ℂ) :
    (s.map (fun w => -w)).prod = (-1) ^ (Multiset.card s) * s.prod := by sorry
