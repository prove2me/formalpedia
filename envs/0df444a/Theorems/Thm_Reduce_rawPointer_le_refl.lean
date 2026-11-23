-- Prove2me | Theorems.Thm_Reduce_rawPointer_le_refl
-- name    : Reduce.rawPointer_le_refl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:59:36.919112+00:00
-- url     : https://prove2.me/theorems/804597dd-f0fd-405b-84ae-22ea74644e64
-- title:
--   Reduce: raw Pointer le refl
-- statement:
--   The Reduce construction uses the raw Pointer le refl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L14-L14
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L14-L14

import Definitions.Def_Bdd_Collect
import Mathlib.Data.Sum.Order
import Definitions.Def_Bdd_Reduce_State
set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Pointer
open Bdd
open RawBdd
open Reduce

theorem Reduce.rawPointer_le_refl (a : RawPointer) : a ≤ a := by sorry
