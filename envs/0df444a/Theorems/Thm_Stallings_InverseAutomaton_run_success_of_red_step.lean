-- Prove2me | Theorems.Thm_Stallings_InverseAutomaton_run_success_of_red_step
-- name    : Stallings.InverseAutomaton.run_success_of_red_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:06:41.080957+00:00
-- url     : https://prove2.me/theorems/fc0641c0-6486-477c-99b8-c89f1589c9e1
-- title:
--   Inverse Automaton: run success of red step
-- statement:
--   A successful traversal remains successful under one free-reduction step.
--
--   Source: https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/InverseAutomaton.lean#L177-L181
-- source:
--   https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/InverseAutomaton.lean#L177-L181

import Mathlib.GroupTheory.FreeGroup.Reduce
import Definitions.Def_Stallings_InverseAutomaton
set_option autoImplicit true
open Stallings
open Stallings.InverseAutomaton
variable {V : Type*} (G : InverseAutomaton V)

theorem Stallings.InverseAutomaton.run_success_of_red_step (v : V) {w z : Word}
    (h : FreeGroup.Red.Step w z) {t : V}
    (hRun : G.run v w = some t) : G.run v z = some t := by sorry
