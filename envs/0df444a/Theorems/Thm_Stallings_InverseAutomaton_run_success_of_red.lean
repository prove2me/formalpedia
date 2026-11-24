-- Prove2me | Theorems.Thm_Stallings_InverseAutomaton_run_success_of_red
-- name    : Stallings.InverseAutomaton.run_success_of_red
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:06:42.468834+00:00
-- url     : https://prove2.me/theorems/a0877c9e-71fd-4ca1-98a3-8afea3ccbee7
-- title:
--   Inverse Automaton: run success of red
-- statement:
--   A successful traversal remains successful after any sequence of free reductions.
--
--   Source: https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/InverseAutomaton.lean#L184-L190
-- source:
--   https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/InverseAutomaton.lean#L184-L190

import Mathlib.GroupTheory.FreeGroup.Reduce
import Definitions.Def_Stallings_InverseAutomaton
set_option autoImplicit true
open Stallings
open Stallings.InverseAutomaton
variable {V : Type*} (G : InverseAutomaton V)

theorem Stallings.InverseAutomaton.run_success_of_red (v : V) {w z : Word}
    (h : FreeGroup.Red w z) {t : V}
    (hRun : G.run v w = some t) : G.run v z = some t := by sorry
