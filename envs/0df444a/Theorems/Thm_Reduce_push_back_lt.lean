-- Prove2me | Theorems.Thm_Reduce_push_back_lt
-- name    : Reduce.push_back_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:09:42.03258+00:00
-- url     : https://prove2.me/theorems/add294cf-250d-4e6e-98d1-b4528fc641a2
-- title:
--   Reduce: push back lt
-- statement:
--   Any node reachable in the pushed heap was already reachable in the original heap,
--       and its index is strictly less than `s` (the pre-push size).
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/Populate.lean#L323-L382
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/Populate.lean#L323-L382

import Definitions.Def_Bdd_Reduce_State
import Definitions.Def_Bdd_Reduce_Populate
set_option autoImplicit true
open Pointer
open Bdd
open RawBdd
open Reduce

theorem Reduce.push_back_lt {n s : Nat} {v : Vector (RawNode n) s} {N : RawNode n}
    {hh  : ∀ k : Fin s,       v[k].Bounded k}
    {hh' : ∀ k : Fin (s + 1), (v.push N)[k].Bounded k}
    {p : RawPointer} (hp : p.Bounded s) {hp' : p.Bounded (s + 1)} :
    ∀ j : Fin (s + 1),
      Pointer.Reachable (cook_heap (v.push N) hh') (p.cook hp') (.node j) →
      ∃ hj : j.1 < s,
        Pointer.Reachable (cook_heap v hh) (p.cook hp) (.node ⟨j.1, hj⟩) := by sorry
