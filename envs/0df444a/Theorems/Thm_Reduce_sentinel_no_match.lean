-- Prove2me | Theorems.Thm_Reduce_sentinel_no_match
-- name    : Reduce.sentinel_no_match
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:13:10.428954+00:00
-- url     : https://prove2.me/theorems/230f2575-75d2-4c08-8fb6-1c132dd210ba
-- title:
--   Reduce: sentinel no match
-- statement:
--   In a non-redundant queue, no entry's key matches the sentinel ⟨.inl false, .inl false⟩.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/Process.lean#L1082-L1092
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/Process.lean#L1082-L1092

import Definitions.Def_Bdd_Reduce_Populate
import Definitions.Def_Bdd_Reduce_Process
set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered RawBdd.RawPointer RawBdd.RawPointer.Bounded Subrelation
open Pointer
open Bdd
open RawBdd
open Reduce

theorem Reduce.sentinel_no_match
    (Q : List ((RawPointer × RawPointer) × Fin m))
    (hnonred : ∀ entry ∈ Q, entry.1.1 ≠ entry.1.2) :
    ∀ entry ∈ Q, entry.1 ≠ ((.inl false : RawPointer), (.inl false : RawPointer)) := by sorry
