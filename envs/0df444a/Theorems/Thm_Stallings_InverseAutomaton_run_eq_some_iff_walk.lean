-- Prove2me | Theorems.Thm_Stallings_InverseAutomaton_run_eq_some_iff_walk
-- name    : Stallings.InverseAutomaton.run_eq_some_iff_walk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:06:41.167261+00:00
-- url     : https://prove2.me/theorems/712f71f6-1793-456a-98e1-6b861989a3a1
-- title:
--   Inverse Automaton: run eq some iff walk
-- statement:
--   The executable traversal returns an endpoint exactly when the corresponding path exists.
--
--   Source: https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/InverseAutomaton.lean#L97-L120
-- source:
--   https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/InverseAutomaton.lean#L97-L120

import Mathlib.GroupTheory.FreeGroup.Reduce
import Definitions.Def_Stallings_InverseAutomaton
set_option autoImplicit true
open Stallings
open Stallings.InverseAutomaton
variable {V : Type*} (G : InverseAutomaton V)

theorem Stallings.InverseAutomaton.run_eq_some_iff_walk {v z : V} {w : Word} :
    G.run v w = some z ↔ G.Walk v w z := by sorry
