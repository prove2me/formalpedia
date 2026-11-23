-- Prove2me | Theorems.Thm_RawBdd_RawPointer_cook_equiv
-- name    : RawBdd.RawPointer.cook_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:55:56.467112+00:00
-- url     : https://prove2.me/theorems/ad3a75c8-2761-432b-883c-9ac35e27ee03
-- title:
--   Raw Pointer: cook equiv
-- statement:
--   The Raw Pointer construction uses the cook equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L2076-L2091
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L2076-L2091

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

theorem RawBdd.RawPointer.cook_equiv {h1 : RawPointer.Bounded m1 p} {h2 : RawPointer.Bounded m2 p} : Pointer.equiv (RawPointer.cook p h1) (RawPointer.cook p h2) := by sorry
