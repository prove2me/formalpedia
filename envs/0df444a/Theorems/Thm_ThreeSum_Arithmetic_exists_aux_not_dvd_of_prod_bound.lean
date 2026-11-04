-- Prove2me | Theorems.Thm_ThreeSum_Arithmetic_exists_aux_not_dvd_of_prod_bound
-- name    : ThreeSum.Arithmetic.exists_aux_not_dvd_of_prod_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:09:53.495591+00:00
-- url     : https://prove2.me/theorems/0fd9dcc6-0c11-4c55-b9c8-5c6e1ef9b9f1
-- title:
--   Arithmetic: exists aux not dvd of prod bound
-- statement:
--   Pairwise coprime auxiliary moduli whose product exceeds the absolute
--   difference separate every nonzero difference.  No primality is necessary.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Arithmetic.lean#L258-L267
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Arithmetic.lean#L258-L267

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

theorem ThreeSum.Arithmetic.exists_aux_not_dvd_of_prod_bound (L : Finset ℤ) (x : ℤ)
    (hcop : (L : Set ℤ).Pairwise (fun a b => IsCoprime a b))
    (hx : x ≠ 0) (hbound : x.natAbs < (∏ l ∈ L, l).natAbs) :
    ∃ l ∈ L, ¬ l ∣ x := by sorry
