-- Prove2me | Theorems.Thm_RawBdd_push_ordered
-- name    : RawBdd.push_ordered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:58:26.587251+00:00
-- url     : https://prove2.me/theorems/c1039525-8129-4aa0-842d-c0b7d153b553
-- title:
--   Raw Bdd: push ordered
-- statement:
--   The Raw Bdd construction uses the push ordered property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L2230-L2247
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L2230-L2247

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

theorem RawBdd.push_ordered : Bdd.Ordered ⟨cook_heap v h0, RawPointer.cook p h1⟩ → Bdd.Ordered ⟨cook_heap (v.push N) h2, RawPointer.cook p h3⟩ := by sorry
