-- Prove2me | Theorems.Thm_Reduce_keyLE_trans
-- name    : Reduce.keyLE_trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:59:43.764595+00:00
-- url     : https://prove2.me/theorems/87945f8f-6a6c-413c-9701-992116506730
-- title:
--   Reduce: key LE trans
-- statement:
--   The Reduce construction uses the key LE trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L51-L85
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L51-L85

import Definitions.Def_Bdd_Collect
import Mathlib.Data.Sum.Order
import Definitions.Def_Bdd_Reduce_State
set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Pointer
open Bdd
open RawBdd
open Reduce

theorem Reduce.keyLE_trans {a b c : RawPointer × RawPointer} : KeyLE a b → KeyLE b c → KeyLE a c := by sorry
