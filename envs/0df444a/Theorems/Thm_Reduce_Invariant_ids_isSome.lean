-- Prove2me | Theorems.Thm_Reduce_Invariant_ids_isSome
-- name    : Reduce.Invariant.ids_isSome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:01:43.687447+00:00
-- url     : https://prove2.me/theorems/683a695b-778d-4e01-a91d-8b33fd5c94e3
-- title:
--   Invariant: ids is Some
-- statement:
--   The Invariant construction uses the ids is Some property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L273-L279
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L273-L279

import Definitions.Def_Bdd_Collect
import Mathlib.Data.Sum.Order
import Definitions.Def_Bdd_Reduce_State
set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Pointer
open Bdd
open RawBdd
open Reduce

theorem Reduce.Invariant.ids_isSome {n m : Nat} {O : OBdd n m} {ps : ProvedState n m}
    {i : Nat} (inv : Invariant O ps i)
    {j : Fin m}
    (hvar  : i < O.1.heap[j].var.1)
    (hreach : Reachable O.1.heap O.1.root (.node j)) :
    (ps.state.ids[j]).isSome := by sorry
