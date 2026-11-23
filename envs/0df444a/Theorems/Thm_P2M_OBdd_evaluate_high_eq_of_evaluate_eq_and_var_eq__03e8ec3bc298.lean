-- Prove2me | Theorems.Thm_P2M_OBdd_evaluate_high_eq_of_evaluate_eq_and_var_eq__03e8ec3bc298
-- name    : P2M_OBdd_evaluate_high_eq_of_evaluate_eq_and_var_eq__03e8ec3bc298
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:59:03.035732+00:00
-- url     : https://prove2.me/theorems/15f6300d-57a0-4718-94aa-b4a616276c39
-- title:
--   P2 M OBdd evaluate high eq of evaluate eq and var eq  03e8ec3bc298: P2 M OBdd evaluate high eq of evaluate eq and var eq  03e8ec3bc298
-- statement:
--   The P2 M OBdd evaluate high eq of evaluate eq and var eq  03e8ec3bc298 construction uses the P2 M OBdd evaluate high eq of evaluate eq and var eq  03e8ec3bc298 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L786-L788
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L786-L788

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

theorem P2M_OBdd_evaluate_high_eq_of_evaluate_eq_and_var_eq__03e8ec3bc298 {n m m' : Nat} {O : OBdd n m} {U : OBdd n m'} {j : Fin m} {i : Fin m'} {ho : O.1.root = node j} {hu : U.1.root = node i} :
    O.evaluate = U.evaluate → O.1.heap[j].var = U.1.heap[i].var → (O.high ho).evaluate = (U.high hu).evaluate := by sorry

alias «OBdd».«evaluate_high_eq_of_evaluate_eq_and_var_eq'» := P2M_OBdd_evaluate_high_eq_of_evaluate_eq_and_var_eq__03e8ec3bc298
