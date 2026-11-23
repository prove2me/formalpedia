-- Prove2me | Theorems.Thm_P2M_Bdd_ordered_of_relevant__4f8ac6a6b318
-- name    : P2M_Bdd_ordered_of_relevant__4f8ac6a6b318
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:02:18.76499+00:00
-- url     : https://prove2.me/theorems/d1956f88-f0fb-4752-a9e2-3db9cf7936b6
-- title:
--   P2 M Bdd ordered of relevant  4f8ac6a6b318: P2 M Bdd ordered of relevant  4f8ac6a6b318
-- statement:
--   The P2 M Bdd ordered of relevant  4f8ac6a6b318 construction uses the P2 M Bdd ordered of relevant  4f8ac6a6b318 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L253-L268
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L253-L268

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

theorem P2M_Bdd_ordered_of_relevant__4f8ac6a6b318 {B : Bdd n m} {h : B.heap = v} {r : B.root = q} :
    B.Ordered → Reachable v q p → Bdd.Ordered {heap := v, root := p} := by sorry

alias «Bdd».«ordered_of_relevant'» := P2M_Bdd_ordered_of_relevant__4f8ac6a6b318
