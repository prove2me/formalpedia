-- Prove2me | Theorems.Thm_Reduce_set_id_ne
-- name    : Reduce.set_id_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:59:52.544902+00:00
-- url     : https://prove2.me/theorems/bd2fc88d-e803-4cb5-9119-6620ead96bdf
-- title:
--   Reduce: set id ne
-- statement:
--   The Reduce construction uses the set id ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L133-L136
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L133-L136

import Definitions.Def_Bdd_Collect
import Mathlib.Data.Sum.Order
import Definitions.Def_Bdd_Reduce_State
set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Pointer
open Bdd
open RawBdd
open Reduce

theorem Reduce.set_id_ne {n m : Nat} (ps : ProvedState n m) (j k : Fin m) (p : RawPointer)
    (h : k ≠ j) : (set_id ps j p).state.ids[k] = ps.state.ids[k] := by sorry
