-- Prove2me | Theorems.Thm_RawBdd_push_evaluate
-- name    : RawBdd.push_evaluate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:58:38.427483+00:00
-- url     : https://prove2.me/theorems/cde19407-f623-4a50-a2b2-eab728a8037d
-- title:
--   Raw Bdd: push evaluate
-- statement:
--   The Raw Bdd construction uses the push evaluate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L2249-L2258
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L2249-L2258

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
open RawBdd

theorem RawBdd.push_evaluate {p : RawPointer} {m : Nat} {hq : p.Bounded m} {n : Nat} {N : RawNode n} {hp : p.Bounded (m + 1)} {v : Vector (RawNode n) m} {h0} {h1} {ho : Bdd.Ordered _} {hu : Bdd.Ordered ⟨cook_heap v h1, RawPointer.cook p hq⟩} :
    OBdd.evaluate ⟨⟨cook_heap (v.push N) h0, RawPointer.cook p hp⟩, ho⟩ =
    OBdd.evaluate ⟨⟨cook_heap v h1, RawPointer.cook p hq⟩, hu⟩ := by sorry
