-- Prove2me | Theorems.Thm_RawBdd_RawNode_cook_equiv
-- name    : RawBdd.RawNode.cook_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:57:31.315236+00:00
-- url     : https://prove2.me/theorems/dfc089fe-fb57-4d35-8548-86bbc0384d00
-- title:
--   Raw Node: cook equiv
-- statement:
--   The Raw Node construction uses the cook equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L2111-L2119
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L2111-L2119

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
open RawBdd

theorem RawBdd.RawNode.cook_equiv : Node.equiv (RawNode.cook N h1) (RawNode.cook N h2) := by sorry
