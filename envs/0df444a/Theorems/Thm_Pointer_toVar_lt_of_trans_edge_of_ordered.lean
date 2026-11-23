-- Prove2me | Theorems.Thm_Pointer_toVar_lt_of_trans_edge_of_ordered
-- name    : Pointer.toVar_lt_of_trans_edge_of_ordered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:05:47.650296+00:00
-- url     : https://prove2.me/theorems/cef1391f-c84c-4d7a-9d0c-376727d99cfd
-- title:
--   Pointer: to Var lt of trans edge of ordered
-- statement:
--   The Pointer construction uses the to Var lt of trans edge of ordered property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1826-L1836
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1826-L1836

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

theorem Pointer.toVar_lt_of_trans_edge_of_ordered :
    Bdd.Ordered ⟨M, x⟩ → Relation.TransGen (Edge M) x y → x.toVar M < y.toVar M := by sorry
