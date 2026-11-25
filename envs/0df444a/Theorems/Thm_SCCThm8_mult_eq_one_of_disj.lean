-- Prove2me | Theorems.Thm_SCCThm8_mult_eq_one_of_disj
-- name    : SCCThm8.mult_eq_one_of_disj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:50:14.10692+00:00
-- url     : https://prove2.me/theorems/fc87d6a6-35e1-5457-bdcc-04910d29ee28
-- title:
--   SCCThm8: mult eq one of disj
-- statement:
--   Three pairwise disjoint `k`-subsets of `Fin (3k)` cover every point exactly once.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Degeneration.lean#L13-L26
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Degeneration.lean#L13-L26

module
public import Definitions.Def_SCCThm8_Rigidity
public import Definitions.Def_SCCThm8_Counting
public import Definitions.Def_SCCThm8_Degeneration
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset

theorem SCCThm8.mult_eq_one_of_disj (k : ℕ) (A B C : Finset (Fin (3 * k)))
    (hA : A.card = k) (hB : B.card = k) (hC : C.card = k)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) (i : Fin (3 * k)) :
    mult A B C i = 1 := by sorry
