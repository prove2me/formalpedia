-- Prove2me | Theorems.Thm_ThreeSum_Arithmetic_early_yes_w3sum_ac885d1
-- name    : ThreeSum.Arithmetic.early_yes_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:14:15.14084+00:00
-- url     : https://prove2.me/theorems/3f770f60-3b6f-4884-bdc7-23638a6f5225
-- title:
--   Arithmetic: early yes
-- statement:
--   If total represented mass exceeds `Rmax * H`, some positive incidence
--   belongs to a true original triple.  The hypotheses bound individual false
--   fibers and the number of false originals, rather than postulating the
--   desired conclusion or a full running-time theorem.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Arithmetic.lean#L305-L351
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Arithmetic.lean#L305-L351

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

theorem ThreeSum.Arithmetic.early_yes_w3sum_ac885d1 {ι τ : Type*} [Fintype τ] [DecidableEq τ]
    (I : Finset ι) (owner : ι → τ) (weight : ι → ℕ)
    (good : τ → Prop) [DecidablePred good] (Rmax H : ℕ)
    (hcap : ∀ t : τ, ¬ good t → fiberWeight I owner weight t ≤ Rmax)
    (hcount : (Finset.univ.filter (fun t : τ => ¬ good t)).card ≤ H)
    (hlarge : Rmax * H < ∑ i ∈ I, weight i) :
    ∃ i ∈ I, 0 < weight i ∧ good (owner i) := by sorry
