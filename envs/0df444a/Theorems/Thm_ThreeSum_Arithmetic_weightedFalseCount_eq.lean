-- Prove2me | Theorems.Thm_ThreeSum_Arithmetic_weightedFalseCount_eq
-- name    : ThreeSum.Arithmetic.weightedFalseCount_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:09:49.362194+00:00
-- url     : https://prove2.me/theorems/93cb715f-a76a-424c-9fbb-1a9b6eccf901
-- title:
--   Arithmetic: weighted False Count eq
-- statement:
--   The actual `H_m = s N_m - sum N_(m*l)` formula, over natural counts.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Arithmetic.lean#L238-L244
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Arithmetic.lean#L238-L244

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

theorem ThreeSum.Arithmetic.weightedFalseCount_eq {ι : Type*} (T : Finset ι) (difference : ι → ℤ)
    (L : Finset ℤ) (m : ℤ)
    (hcop : ∀ l ∈ L, ∃ u v : ℤ, u * m + v * l = 1) :
    weightedFalseCount T difference L m =
      L.card * modCount T difference m - (∑ l ∈ L, modCount T difference (m * l)) := by sorry
