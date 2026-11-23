-- Prove2me | Theorems.Thm_Pointer_Reachable_iff
-- name    : Pointer.Reachable_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:58:11.951288+00:00
-- url     : https://prove2.me/theorems/34ca94ba-532c-4e65-96a8-cf52b0d7638e
-- title:
--   Pointer: Reachable iff
-- statement:
--   The Pointer construction uses the Reachable iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L972-L1002
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L972-L1002

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered

theorem Pointer.Reachable_iff {M : Vector (Node n m) m } :
  Pointer.Reachable M r p ↔ (r = p ∨ (∃ j, r = .node j ∧ (Pointer.Reachable M M[j].low p ∨ Pointer.Reachable M M[j].high p))) := by sorry
