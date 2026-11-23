-- Prove2me | Theorems.Thm_RawBdd_cook_high
-- name    : RawBdd.cook_high
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:58:24.073015+00:00
-- url     : https://prove2.me/theorems/7f7a475c-3948-43d2-9fa2-3330c8ce9154
-- title:
--   Raw Bdd: cook high
-- statement:
--   The Raw Bdd construction uses the cook high property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L2131-L2131
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L2131-L2131

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

theorem RawBdd.cook_high {rn : RawNode n} {h1} {h2} : rn.hi.cook (m := m) h1 = (rn.cook h2).high := by sorry
