-- Prove2me | Theorems.Thm_P2M_OBdd_evaluate_node__1867d6ba89de
-- name    : P2M_OBdd_evaluate_node__1867d6ba89de
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:00:05.95081+00:00
-- url     : https://prove2.me/theorems/190912fd-7c95-4ca9-9709-a91487303b30
-- title:
--   P2 M OBdd evaluate node  1867d6ba89de: P2 M OBdd evaluate node  1867d6ba89de
-- statement:
--   The P2 M OBdd evaluate node  1867d6ba89de construction uses the P2 M OBdd evaluate node  1867d6ba89de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L638-L647
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L638-L647

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

theorem P2M_OBdd_evaluate_node__1867d6ba89de {n m} {v : Vector (Node n m) m} {j : Fin m} {h} : OBdd.evaluate ⟨{ heap := v, root := node j }, h⟩ = fun I ↦
    if I[v[j].var]
    then OBdd.evaluate ⟨{ heap := v, root := v[j].high }, OBdd.ordered_of_high_edge h⟩ I
    else OBdd.evaluate ⟨{ heap := v, root := v[j].low }, OBdd.ordered_of_low_edge h⟩ I := by sorry

alias «OBdd».«evaluate_node'» := P2M_OBdd_evaluate_node__1867d6ba89de
