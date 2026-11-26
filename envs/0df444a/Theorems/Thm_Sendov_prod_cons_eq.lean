-- Prove2me | Theorems.Thm_Sendov_prod_cons_eq
-- name    : Sendov.prod_cons_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:52:23.606489+00:00
-- url     : https://prove2.me/theorems/eb5064e7-94ea-4fca-a9a8-713ad1d15842
-- title:
--   Sendov: prod cons eq
-- statement:
--   The factorization of `p`, with `a` put back into the multiset.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Counterexample/Identities.lean#L51-L54
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Counterexample/Identities.lean#L51-L54

import Definitions.Def_Sendov_Counterexample_Factor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Sendov_Counterexample_Identities
set_option autoImplicit false
open Sendov
open Polynomial Multiset
variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ} {p : ℂ[X]}

theorem Sendov.prod_cons_eq (a : ℂ) (z : Multiset ℂ) :
    (X - C a) * (z.map (fun w => X - C w)).prod
      = ((a ::ₘ z).map (fun w => X - C w)).prod := by sorry
