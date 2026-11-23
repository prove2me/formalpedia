-- Prove2me | Theorems.Thm_P2M_OBdd_toTree_terminal__6f80b985dd51
-- name    : P2M_OBdd_toTree_terminal__6f80b985dd51
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:55:11.984457+00:00
-- url     : https://prove2.me/theorems/b893837f-52e0-44cc-a6bd-3948dd388d26
-- title:
--   P2 M OBdd to Tree terminal  6f80b985dd51: P2 M OBdd to Tree terminal  6f80b985dd51
-- statement:
--   The P2 M OBdd to Tree terminal  6f80b985dd51 construction uses the P2 M OBdd to Tree terminal  6f80b985dd51 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L663-L666
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L663-L666

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

theorem P2M_OBdd_toTree_terminal__6f80b985dd51 {n m} {O : OBdd n m} : O.1.root = terminal b → O.toTree = .leaf b := by sorry

alias «OBdd».«toTree_terminal'» := P2M_OBdd_toTree_terminal__6f80b985dd51
