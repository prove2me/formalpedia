-- Prove2me | Theorems.Thm_Reduce_rawPointer_le_trans
-- name    : Reduce.rawPointer_le_trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:01:16.412269+00:00
-- url     : https://prove2.me/theorems/6bc4d8cd-29c9-4d5b-8314-9676f6e83aeb
-- title:
--   Reduce: raw Pointer le trans
-- statement:
--   The Reduce construction uses the raw Pointer le trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L16-L16
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L16-L16

import Definitions.Def_Bdd_Collect
import Mathlib.Data.Sum.Order
import Definitions.Def_Bdd_Reduce_State
set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Pointer
open Bdd
open RawBdd
open Reduce

theorem Reduce.rawPointer_le_trans {a b c : RawPointer} : a ≤ b → b ≤ c → a ≤ c := by sorry
