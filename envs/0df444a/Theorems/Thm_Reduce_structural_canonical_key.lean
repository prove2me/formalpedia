-- Prove2me | Theorems.Thm_Reduce_structural_canonical_key
-- name    : Reduce.structural_canonical_key
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:01:34.59494+00:00
-- url     : https://prove2.me/theorems/a38645e8-6722-4b5e-8c86-32e81f39925a
-- title:
--   Reduce: structural canonical key
-- statement:
--   Injectivity of `toTree` for sub-BDDs sharing the same heap, given heap index-injectivity.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L152-L199
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/State.lean#L152-L199

import Definitions.Def_Bdd_Collect
import Mathlib.Data.Sum.Order
import Definitions.Def_Bdd_Reduce_State
set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Pointer
open Bdd
open RawBdd
open Reduce

theorem Reduce.structural_canonical_key {n s : Nat} {M : Vector (Node n s) s}
    (node_inj : ∀ (kp kq : Fin s),
        M[kp].var = M[kq].var → M[kp].low = M[kq].low → M[kp].high = M[kq].high → kp = kq) :
    ∀ (P Q : OBdd n s), P.1.heap = M → Q.1.heap = M →
      OBdd.toTree P = OBdd.toTree Q → P.1.root = Q.1.root := by sorry
