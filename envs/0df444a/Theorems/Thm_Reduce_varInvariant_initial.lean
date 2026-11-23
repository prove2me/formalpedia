-- Prove2me | Theorems.Thm_Reduce_varInvariant_initial
-- name    : Reduce.varInvariant_initial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:01:47.486597+00:00
-- url     : https://prove2.me/theorems/fd730fdd-1cee-4f0f-ad40-7928302bd2d5
-- title:
--   Reduce: var Invariant initial
-- statement:
--   The Reduce construction uses the var Invariant initial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L294-L297
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L294-L297

import Definitions.Def_Bdd_Collect
import Mathlib.Data.Sum.Order
import Definitions.Def_Bdd_Reduce_State
set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Pointer
open Bdd
open RawBdd
open Reduce

theorem Reduce.varInvariant_initial {n m : Nat} {O : OBdd n m} :
    VarInvariant O (provedStateInitial n m) := by sorry
