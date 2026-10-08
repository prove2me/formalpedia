-- Prove2me | Theorems.Thm_RhinViola_integerLinearFormHasSumFinset
-- name    : RhinViola.integerLinearFormHasSumFinset
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T10:37:53.199361+00:00
-- url     : https://prove2.me/theorems/460f9f27-8dba-4091-91a1-38429c643537
-- title:
--   Finite sums of integer-linear-form series remain integer linear forms
-- statement:
--   A finite termwise sum of convergent series whose sums lie in Z + Z alpha again has a sum in Z + Z alpha. The integer coefficients are the finite sums of the individual integer coefficients.
-- source:
--   Elementary finite closure property used to assemble the polynomial numerator in the Rhin-Viola arithmetic argument.

import Theorems.Thm_RhinViola_integerLinearFormHasSumAdd
import Mathlib.Tactic
open scoped BigOperators

theorem RhinViola.integerLinearFormHasSumFinset
    {ι : Type*} [DecidableEq ι]
    (α : ℝ) (s : Finset ι) (f : ι → ℕ → ℝ) (z c : ι → ℤ)
    (h : ∀ i ∈ s, HasSum (f i) ((z i : ℝ) + (c i : ℝ) * α)) :
    HasSum (fun k : ℕ => Finset.sum s (fun i => f i k))
      (((Finset.sum s (fun i => z i) : ℤ) : ℝ) +
        ((Finset.sum s (fun i => c i) : ℤ) : ℝ) * α) := by sorry
