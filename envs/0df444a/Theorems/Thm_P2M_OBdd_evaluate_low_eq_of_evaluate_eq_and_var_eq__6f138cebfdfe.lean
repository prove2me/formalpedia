-- Prove2me | Theorems.Thm_P2M_OBdd_evaluate_low_eq_of_evaluate_eq_and_var_eq__6f138cebfdfe
-- name    : P2M_OBdd_evaluate_low_eq_of_evaluate_eq_and_var_eq__6f138cebfdfe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:59:10.543433+00:00
-- url     : https://prove2.me/theorems/15ff5991-4925-4916-b64c-4799bc7ac972
-- title:
--   P2 M OBdd evaluate low eq of evaluate eq and var eq  6f138cebfdfe: P2 M OBdd evaluate low eq of evaluate eq and var eq  6f138cebfdfe
-- statement:
--   The P2 M OBdd evaluate low eq of evaluate eq and var eq  6f138cebfdfe construction uses the P2 M OBdd evaluate low eq of evaluate eq and var eq  6f138cebfdfe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L793-L795
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L793-L795

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

theorem P2M_OBdd_evaluate_low_eq_of_evaluate_eq_and_var_eq__6f138cebfdfe {n m m' : Nat} {O : OBdd n m} {U : OBdd n m'} {j : Fin m} {i : Fin m'} {ho : O.1.root = node j} {hu : U.1.root = node i} :
  O.evaluate = U.evaluate → O.1.heap[j].var = U.1.heap[i].var → (O.low ho).evaluate = (U.low hu).evaluate := by sorry

alias «OBdd».«evaluate_low_eq_of_evaluate_eq_and_var_eq'» := P2M_OBdd_evaluate_low_eq_of_evaluate_eq_and_var_eq__6f138cebfdfe
