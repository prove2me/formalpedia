-- Prove2me | Theorems.Thm_P2M_OBdd_card_reachable_node__da57529a8d4b
-- name    : P2M_OBdd_card_reachable_node__da57529a8d4b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:00:23.23826+00:00
-- url     : https://prove2.me/theorems/23a86f75-f08f-405b-ab86-3ce969682d9f
-- title:
--   P2 M OBdd card reachable node  da57529a8d4b: P2 M OBdd card reachable node  da57529a8d4b
-- statement:
--   The P2 M OBdd card reachable node  da57529a8d4b construction uses the P2 M OBdd card reachable node  da57529a8d4b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1182-L1190
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1182-L1190

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

theorem P2M_OBdd_card_reachable_node__da57529a8d4b {O : OBdd n m} (h : O.1.root = node j) :
  Fintype.card {p // Reachable O.1.heap O.1.root p} =
  Fintype.card {p // p = O.1.root ∨ (Reachable O.1.heap (O.low  h).1.root p ∨ Reachable O.1.heap (O.high h).1.root p)} := by sorry

alias «OBdd».«card_reachable_node'» := P2M_OBdd_card_reachable_node__da57529a8d4b
