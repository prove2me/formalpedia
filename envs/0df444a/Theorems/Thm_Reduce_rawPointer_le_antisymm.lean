-- Prove2me | Theorems.Thm_Reduce_rawPointer_le_antisymm
-- name    : Reduce.rawPointer_le_antisymm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:59:39.370552+00:00
-- url     : https://prove2.me/theorems/039680f6-6a9b-4e43-9cb1-66fa7118cb99
-- title:
--   Reduce: raw Pointer le antisymm
-- statement:
--   The Reduce construction uses the raw Pointer le antisymm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L17-L17
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L17-L17

import Definitions.Def_Bdd_Collect
import Mathlib.Data.Sum.Order
import Definitions.Def_Bdd_Reduce_State
set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Pointer
open Bdd
open RawBdd
open Reduce

theorem Reduce.rawPointer_le_antisymm {a b : RawPointer} : a ≤ b → b ≤ a → a = b := by sorry
