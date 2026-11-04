-- Prove2me | Theorems.Thm_ThreeSum_Arithmetic_falseCount_le_weightedFalseCount
-- name    : ThreeSum.Arithmetic.falseCount_le_weightedFalseCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:09:57.433537+00:00
-- url     : https://prove2.me/theorems/029f2cbc-c7e6-4dcd-a42f-f26e1ca876bb
-- title:
--   Arithmetic: false Count le weighted False Count
-- statement:
--   Auxiliary tests separating every nonzero input difference make the
--   weighted score an upper bound on the number of false modular triples.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Arithmetic.lean#L271-L283
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Arithmetic.lean#L271-L283

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Arithmetic
set_option autoImplicit false
open ThreeSum ThreeSum.Arithmetic
open Finset
open scoped BigOperators

theorem ThreeSum.Arithmetic.falseCount_le_weightedFalseCount {ι : Type*} (T : Finset ι)
    (difference : ι → ℤ) (L : Finset ℤ) (m : ℤ)
    (hsep : ∀ i ∈ T, difference i ≠ 0 → ∃ l ∈ L, ¬ l ∣ difference i) :
    (∑ i ∈ T, if m ∣ difference i ∧ difference i ≠ 0 then (1 : ℕ) else 0) ≤
      weightedFalseCount T difference L m := by sorry
