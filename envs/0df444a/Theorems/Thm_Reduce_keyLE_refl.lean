-- Prove2me | Theorems.Thm_Reduce_keyLE_refl
-- name    : Reduce.keyLE_refl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:01:18.473822+00:00
-- url     : https://prove2.me/theorems/f224f54a-7b14-41e2-b915-10d04a2fc0c6
-- title:
--   Reduce: key LE refl
-- statement:
--   The Reduce construction uses the key LE refl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L24-L27
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L24-L27

import Definitions.Def_Bdd_Collect
import Mathlib.Data.Sum.Order
import Definitions.Def_Bdd_Reduce_State
set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Pointer
open Bdd
open RawBdd
open Reduce

theorem Reduce.keyLE_refl (a : RawPointer × RawPointer) : KeyLE a a := by sorry
