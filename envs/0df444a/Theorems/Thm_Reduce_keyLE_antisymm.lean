-- Prove2me | Theorems.Thm_Reduce_keyLE_antisymm
-- name    : Reduce.keyLE_antisymm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:01:19.15322+00:00
-- url     : https://prove2.me/theorems/8d4255b4-6018-4988-b1e9-7748309f5cb1
-- title:
--   Reduce: key LE antisymm
-- statement:
--   The Reduce construction uses the key LE antisymm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L41-L49
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L41-L49

import Definitions.Def_Bdd_Collect
import Mathlib.Data.Sum.Order
import Definitions.Def_Bdd_Reduce_State
set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Pointer
open Bdd
open RawBdd
open Reduce

theorem Reduce.keyLE_antisymm {a b : RawPointer × RawPointer} : KeyLE a b → KeyLE b a → a = b := by sorry
