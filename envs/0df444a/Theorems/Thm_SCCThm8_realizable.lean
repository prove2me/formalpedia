-- Prove2me | Theorems.Thm_SCCThm8_realizable
-- name    : SCCThm8.realizable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:50:27.713069+00:00
-- url     : https://prove2.me/theorems/fd0d3e82-3020-432d-b9bb-08fd35c39e4b
-- title:
--   SCCThm8: realizable
-- statement:
--   **Realizability (Lemma 2).** Every `m ∈ {0,1,2,3}^(3k)` with `∑ m = 3k` is the multiplicity
--   vector of some triple of `k`-subsets.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Counting.lean#L68-L84
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Counting.lean#L68-L84

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Counting
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset

theorem SCCThm8.realizable (k : ℕ) (m : Fin (3 * k) → ℤ) (hm : ∀ i, 0 ≤ m i ∧ m i ≤ 3)
    (hs : ∑ i, m i = 3 * k) :
    ∃ A B C : Finset (Fin (3 * k)), A.card = k ∧ B.card = k ∧ C.card = k ∧
      ∀ i, mult A B C i = m i := by sorry
