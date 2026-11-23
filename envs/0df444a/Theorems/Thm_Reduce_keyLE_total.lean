-- Prove2me | Theorems.Thm_Reduce_keyLE_total
-- name    : Reduce.keyLE_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:01:18.051067+00:00
-- url     : https://prove2.me/theorems/1526f4f9-9dcd-4aa7-942c-29bbd34d16dc
-- title:
--   Reduce: key LE total
-- statement:
--   The Reduce construction uses the key LE total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L29-L39
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L29-L39

import Definitions.Def_Bdd_Collect
import Mathlib.Data.Sum.Order
import Definitions.Def_Bdd_Reduce_State
set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Pointer
open Bdd
open RawBdd
open Reduce

theorem Reduce.keyLE_total (a b : RawPointer × RawPointer) : KeyLE a b ∨ KeyLE b a := by sorry
