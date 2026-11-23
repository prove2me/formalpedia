-- Prove2me | Theorems.Thm_P2M_OBdd_reachable_from_node_iff__59148aa8fc2a
-- name    : P2M_OBdd_reachable_from_node_iff__59148aa8fc2a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:00:21.968+00:00
-- url     : https://prove2.me/theorems/e49906a5-1749-45ea-b889-9916bb72f2b5
-- title:
--   P2 M OBdd reachable from node iff  59148aa8fc2a: P2 M OBdd reachable from node iff  59148aa8fc2a
-- statement:
--   The P2 M OBdd reachable from node iff  59148aa8fc2a construction uses the P2 M OBdd reachable from node iff  59148aa8fc2a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1141-L1180
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1141-L1180

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

theorem P2M_OBdd_reachable_from_node_iff__59148aa8fc2a {O : OBdd n m} (h : O.1.root = node j) :
    Reachable O.1.heap O.1.root p ↔ p = O.1.root ∨ (Reachable O.1.heap (O.low h).1.root p ∨ Reachable O.1.heap (O.high h).1.root p) := by sorry

alias «OBdd».«reachable_from_node_iff'» := P2M_OBdd_reachable_from_node_iff__59148aa8fc2a
