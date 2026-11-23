-- Prove2me | Theorems.Thm_Reduce_rawPointer_le_total
-- name    : Reduce.rawPointer_le_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:01:09.791824+00:00
-- url     : https://prove2.me/theorems/9f8f1a26-4b6f-43fd-9803-15ff9fe0d204
-- title:
--   Reduce: raw Pointer le total
-- statement:
--   The Reduce construction uses the raw Pointer le total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L15-L15
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L15-L15

import Definitions.Def_Bdd_Collect
import Mathlib.Data.Sum.Order
import Definitions.Def_Bdd_Reduce_State
set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Pointer
open Bdd
open RawBdd
open Reduce

theorem Reduce.rawPointer_le_total (a b : RawPointer) : a ≤ b ∨ b ≤ a := by sorry
