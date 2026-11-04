-- Prove2me | Theorems.Thm_ThreeSum_Arithmetic_sum_fiberWeight
-- name    : ThreeSum.Arithmetic.sum_fiberWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:14:11.466891+00:00
-- url     : https://prove2.me/theorems/1935bd50-a0ac-4d64-8134-7b238a677ec4
-- title:
--   Arithmetic: sum fiber Weight
-- statement:
--   The Arithmetic construction uses the sum fiber Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Arithmetic.lean#L291-L299
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Arithmetic.lean#L291-L299

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

theorem ThreeSum.Arithmetic.sum_fiberWeight {ι τ : Type*} [Fintype τ] [DecidableEq τ]
    (I : Finset ι) (owner : ι → τ) (weight : ι → ℕ) :
    (∑ t : τ, fiberWeight I owner weight t) = ∑ i ∈ I, weight i := by sorry
