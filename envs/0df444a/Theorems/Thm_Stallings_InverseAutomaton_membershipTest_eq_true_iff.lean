-- Prove2me | Theorems.Thm_Stallings_InverseAutomaton_membershipTest_eq_true_iff
-- name    : Stallings.InverseAutomaton.membershipTest_eq_true_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:06:38.355957+00:00
-- url     : https://prove2.me/theorems/ea5e2850-6682-42fa-9c2d-76b25e16d0fb
-- title:
--   Inverse Automaton: membership Test eq true iff
-- statement:
--   The Inverse Automaton construction uses the membership Test eq true iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/InverseAutomaton.lean#L244-L246
-- source:
--   https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/InverseAutomaton.lean#L244-L246

import Mathlib.GroupTheory.FreeGroup.Reduce
import Definitions.Def_Stallings_InverseAutomaton
set_option autoImplicit true
open Stallings
open Stallings.InverseAutomaton
variable {V : Type*} (G : InverseAutomaton V)

theorem Stallings.InverseAutomaton.membershipTest_eq_true_iff [DecidableEq V] (G : InverseAutomaton V) (g : Free) :
    G.membershipTest g = true ↔ g ∈ G.loopSubgroup := by sorry
