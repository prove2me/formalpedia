-- Prove2me | Theorems.Thm_Stallings_InverseAutomaton_accepts_iff_mem_loopSubgroup
-- name    : Stallings.InverseAutomaton.accepts_iff_mem_loopSubgroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:06:40.155229+00:00
-- url     : https://prove2.me/theorems/fce2d8ce-9e50-4886-a04c-fc4706122da1
-- title:
--   Inverse Automaton: accepts iff mem loop Subgroup
-- statement:
--   The Inverse Automaton construction uses the accepts iff mem loop Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/InverseAutomaton.lean#L217-L237
-- source:
--   https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/InverseAutomaton.lean#L217-L237

import Mathlib.GroupTheory.FreeGroup.Reduce
import Definitions.Def_Stallings_InverseAutomaton
set_option autoImplicit true
open Stallings
open Stallings.InverseAutomaton
variable {V : Type*} (G : InverseAutomaton V)

theorem Stallings.InverseAutomaton.accepts_iff_mem_loopSubgroup (g : Free) :
    G.accepts g ↔ g ∈ G.loopSubgroup := by sorry
