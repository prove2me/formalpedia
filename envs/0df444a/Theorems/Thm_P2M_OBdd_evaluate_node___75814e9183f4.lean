-- Prove2me | Theorems.Thm_P2M_OBdd_evaluate_node___75814e9183f4
-- name    : P2M_OBdd_evaluate_node___75814e9183f4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:55:10.168796+00:00
-- url     : https://prove2.me/theorems/764a01f0-7683-46ac-87ef-e3822a341d75
-- title:
--   P2 M OBdd evaluate node   75814e9183f4: P2 M OBdd evaluate node   75814e9183f4
-- statement:
--   The P2 M OBdd evaluate node   75814e9183f4 construction uses the P2 M OBdd evaluate node   75814e9183f4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L684-L688
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L684-L688

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

theorem P2M_OBdd_evaluate_node___75814e9183f4 {n m} {O : OBdd n m} {j : Fin m} (h : O.1.root = node j) :
    O.evaluate = fun I ↦ if I[O.1.heap[j].var] then (O.high h).evaluate I else (O.low h).evaluate I := by sorry

alias «OBdd».«evaluate_node''» := P2M_OBdd_evaluate_node___75814e9183f4
