-- Prove2me | Theorems.Thm_Stallings_InverseAutomaton_run_success_cancel
-- name    : Stallings.InverseAutomaton.run_success_cancel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:06:41.425968+00:00
-- url     : https://prove2.me/theorems/6e832e31-9739-45db-8805-a635d2fca5b6
-- title:
--   Inverse Automaton: run success cancel
-- statement:
--   A successful traversal remains successful after cancelling a letter pair.
--
--   Source: https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/InverseAutomaton.lean#L158-L174
-- source:
--   https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/InverseAutomaton.lean#L158-L174

import Mathlib.GroupTheory.FreeGroup.Reduce
import Definitions.Def_Stallings_InverseAutomaton
set_option autoImplicit true
open Stallings
open Stallings.InverseAutomaton
variable {V : Type*} (G : InverseAutomaton V)

theorem Stallings.InverseAutomaton.run_success_cancel (v : V) (pre suffix : Word) (x : Letter)
    {z : V}
    (h : G.run v (pre ++ x :: letterInv x :: suffix) = some z) :
    G.run v (pre ++ suffix) = some z := by sorry
