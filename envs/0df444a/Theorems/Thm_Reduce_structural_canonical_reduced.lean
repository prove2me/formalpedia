-- Prove2me | Theorems.Thm_Reduce_structural_canonical_reduced
-- name    : Reduce.structural_canonical_reduced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:01:39.591559+00:00
-- url     : https://prove2.me/theorems/b0866714-aba7-44b4-8832-c5b0639d5fbe
-- title:
--   Reduce: structural canonical reduced
-- statement:
--   In a structurally canonical heap (no two positions have the same raw node),
--       any ordered BDD is reduced.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L203-L248
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L203-L248

import Definitions.Def_Bdd_Collect
import Mathlib.Data.Sum.Order
import Definitions.Def_Bdd_Reduce_State
set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Pointer
open Bdd
open RawBdd
open Reduce

theorem Reduce.structural_canonical_reduced {n s : Nat}
    {v : Vector (RawNode n) s} {hh : ∀ k : Fin s, v[k].Bounded k}
    (hsc : ∀ k1 k2 : Fin s, v[k1] = v[k2] → k1 = k2)
    {root : Pointer s}
    (hord : Bdd.Ordered ⟨cook_heap v hh, root⟩)
    (hnored : Bdd.NoRedundancy ⟨cook_heap v hh, root⟩) :
    OBdd.Reduced ⟨⟨cook_heap v hh, root⟩, hord⟩ := by sorry
