-- Prove2me | Theorems.Thm_Stallings_InverseAutomaton_run_append
-- name    : Stallings.InverseAutomaton.run_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:06:41.564689+00:00
-- url     : https://prove2.me/theorems/94567f52-5bb7-45a4-ae79-15f8fcb05098
-- title:
--   Inverse Automaton: run append
-- statement:
--   Traversal distributes over concatenation of words.
--
--   Source: https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/InverseAutomaton.lean#L143-L155
-- source:
--   https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/InverseAutomaton.lean#L143-L155

import Mathlib.GroupTheory.FreeGroup.Reduce
import Definitions.Def_Stallings_InverseAutomaton
set_option autoImplicit true
open Stallings
open Stallings.InverseAutomaton
variable {V : Type*} (G : InverseAutomaton V)

theorem Stallings.InverseAutomaton.run_append (v : V) (u z : Word) :
    G.run v (u ++ z) = (G.run v u).bind fun t => G.run t z := by sorry
