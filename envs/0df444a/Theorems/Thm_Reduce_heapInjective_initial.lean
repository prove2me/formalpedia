-- Prove2me | Theorems.Thm_Reduce_heapInjective_initial
-- name    : Reduce.heapInjective_initial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:01:52.487116+00:00
-- url     : https://prove2.me/theorems/9eb97538-5213-443b-9277-7e59fb8f63ef
-- title:
--   Reduce: heap Injective initial
-- statement:
--   The Reduce construction uses the heap Injective initial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L304-L307
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L304-L307

import Definitions.Def_Bdd_Collect
import Mathlib.Data.Sum.Order
import Definitions.Def_Bdd_Reduce_State
set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Pointer
open Bdd
open RawBdd
open Reduce

theorem Reduce.heapInjective_initial {n m : Nat} :
    HeapInjective (provedStateInitial n m) := by sorry
