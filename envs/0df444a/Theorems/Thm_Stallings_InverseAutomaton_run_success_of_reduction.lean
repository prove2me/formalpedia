-- Prove2me | Theorems.Thm_Stallings_InverseAutomaton_run_success_of_reduction
-- name    : Stallings.InverseAutomaton.run_success_of_reduction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:06:43.393276+00:00
-- url     : https://prove2.me/theorems/f6bbf0a3-5a88-4661-ba3a-261ba7ca58f2
-- title:
--   Inverse Automaton: run success of reduction
-- statement:
--   A successful traversal remains successful on the canonical reduced word.
--
--   Source: https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/InverseAutomaton.lean#L193-L196
-- source:
--   https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/InverseAutomaton.lean#L193-L196

import Mathlib.GroupTheory.FreeGroup.Reduce
import Definitions.Def_Stallings_InverseAutomaton
set_option autoImplicit true
open Stallings
open Stallings.InverseAutomaton
variable {V : Type*} (G : InverseAutomaton V)

theorem Stallings.InverseAutomaton.run_success_of_reduction (v : V) (w : Word) {t : V}
    (hRun : G.run v w = some t) :
    G.run v (FreeGroup.reduce w) = some t := by sorry
