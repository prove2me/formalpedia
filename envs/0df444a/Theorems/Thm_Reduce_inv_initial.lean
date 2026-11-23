-- Prove2me | Theorems.Thm_Reduce_inv_initial
-- name    : Reduce.inv_initial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:01:35.944372+00:00
-- url     : https://prove2.me/theorems/bb6a91fb-bed2-4dbd-a2f9-3647709a35c7
-- title:
--   Reduce: inv initial
-- statement:
--   The Reduce construction uses the inv initial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L267-L271
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L267-L271

import Definitions.Def_Bdd_Collect
import Mathlib.Data.Sum.Order
import Definitions.Def_Bdd_Reduce_State
set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Pointer
open Bdd
open RawBdd
open Reduce

theorem Reduce.inv_initial {n m : Nat} {O : OBdd n m} {i : Nat}
    (hi : ∀ j : Fin m, O.1.heap[j].var.1 ≤ i) :
    Invariant O (provedStateInitial n m) i := by sorry
