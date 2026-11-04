-- Prove2me | Theorems.Thm_ThreeSum_Arithmetic_missWeight_pos_of_witness
-- name    : ThreeSum.Arithmetic.missWeight_pos_of_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:09:52.262406+00:00
-- url     : https://prove2.me/theorems/d9372a60-eb21-431d-9705-efc0ffce85c0
-- title:
--   Arithmetic: miss Weight pos of witness
-- statement:
--   The Arithmetic construction uses the miss Weight pos of witness property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Arithmetic.lean#L246-L251
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Arithmetic.lean#L246-L251

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

theorem ThreeSum.Arithmetic.missWeight_pos_of_witness {L : Finset ℤ} {x l : ℤ}
    (hl : l ∈ L) (hnot : ¬ l ∣ x) : 1 ≤ missWeight L x := by sorry
