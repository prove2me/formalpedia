-- Prove2me | Theorems.Thm_P2M_selection_seq_prop__c83e968fc7f1
-- name    : P2M_selection_seq_prop__c83e968fc7f1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:09:16.318136+00:00
-- url     : https://prove2.me/theorems/c5df430a-ac6d-45bd-b30e-c9672a6e67ac
-- title:
--   P2 M selection seq prop  c83e968fc7f1: P2 M selection seq prop  c83e968fc7f1
-- statement:
--   The P2 M selection seq prop  c83e968fc7f1 construction uses the P2 M selection seq prop  c83e968fc7f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Mathlib/InfGraphRamsey.lean#L70-L81
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Mathlib/InfGraphRamsey.lean#L70-L81

import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic
import Definitions.Def_AutomataTheory_Mathlib_InfGraphRamsey
set_option autoImplicit true
open Function Set
open Classical
variable {Color Vertex : Type*} [Finite Color]
variable (color : (e : Edge) → Color)
variable [Infinite Vertex]

theorem P2M_selection_seq_prop__c83e968fc7f1 (n : ℕ) :
    ∃ ivs : InfVSet Vertex, selection_prop color ivs (selection_seq color n) ∧
      (ivs.set = ⋂ m < n, (selection_seq color m).vs.set) := by sorry

alias «selection_seq_prop'» := P2M_selection_seq_prop__c83e968fc7f1
