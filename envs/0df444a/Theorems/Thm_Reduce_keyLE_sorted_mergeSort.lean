-- Prove2me | Theorems.Thm_Reduce_keyLE_sorted_mergeSort
-- name    : Reduce.keyLE_sorted_mergeSort
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:01:24.518802+00:00
-- url     : https://prove2.me/theorems/e177faa4-b51f-4659-897e-2a0858596196
-- title:
--   Reduce: key LE sorted merge Sort
-- statement:
--   The Reduce construction uses the key LE sorted merge Sort property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L87-L99
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L87-L99

import Definitions.Def_Bdd_Collect
import Mathlib.Data.Sum.Order
import Definitions.Def_Bdd_Reduce_State
set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Pointer
open Bdd
open RawBdd
open Reduce

theorem Reduce.keyLE_sorted_mergeSort {m : Nat}
    (l : List ((RawPointer × RawPointer) × Fin m)) :
    (l.mergeSort (fun a b => leKeyPair a.1 b.1)).Pairwise (fun a b => KeyLE a.1 b.1) := by sorry
