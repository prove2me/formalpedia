-- Prove2me | Theorems.Thm_Reduce_allAbove_initial
-- name    : Reduce.allAbove_initial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:01:48.195212+00:00
-- url     : https://prove2.me/theorems/c4549410-1ccd-4802-9662-66ef8f1f948f
-- title:
--   Reduce: all Above initial
-- statement:
--   The Reduce construction uses the all Above initial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L299-L302
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L299-L302

import Definitions.Def_Bdd_Collect
import Mathlib.Data.Sum.Order
import Definitions.Def_Bdd_Reduce_State
set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Pointer
open Bdd
open RawBdd
open Reduce

theorem Reduce.allAbove_initial {n m : Nat} {i : Nat} :
    AllAbove (provedStateInitial n m) i := by sorry
