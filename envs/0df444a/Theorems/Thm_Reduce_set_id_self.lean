-- Prove2me | Theorems.Thm_Reduce_set_id_self
-- name    : Reduce.set_id_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:59:51.950902+00:00
-- url     : https://prove2.me/theorems/8782715f-1513-496e-9c3f-6aef517d8a6d
-- title:
--   Reduce: set id self
-- statement:
--   The Reduce construction uses the set id self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L128-L131
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L128-L131

import Definitions.Def_Bdd_Collect
import Mathlib.Data.Sum.Order
import Definitions.Def_Bdd_Reduce_State
set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Pointer
open Bdd
open RawBdd
open Reduce

theorem Reduce.set_id_self {n m : Nat} (ps : ProvedState n m) (j : Fin m) (p : RawPointer) :
    (set_id ps j p).state.ids[j] = some p := by sorry
