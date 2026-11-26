-- Prove2me | Theorems.Thm_Sendov_sumEraseProd_cons
-- name    : Sendov.sumEraseProd_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:52:35.867809+00:00
-- url     : https://prove2.me/theorems/69fbc6bc-6bd6-4fe4-bfa1-78628a79929e
-- title:
--   Sendov: sum Erase Prod cons
-- statement:
--   Splitting off one element, exactly as `Multiset.esymm` does at the top index.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Counterexample/Identities.lean#L106-L113
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Counterexample/Identities.lean#L106-L113

import Definitions.Def_Sendov_Counterexample_Factor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Sendov_Counterexample_Identities
set_option autoImplicit false
open Sendov
open Polynomial Multiset
variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ} {p : ℂ[X]}
open scoped Classical

theorem Sendov.sumEraseProd_cons (v : ℂ) (t : Multiset ℂ) :
    sumEraseProd (v ::ₘ t) = t.prod + v * sumEraseProd t := by sorry
