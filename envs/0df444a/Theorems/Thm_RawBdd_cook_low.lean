-- Prove2me | Theorems.Thm_RawBdd_cook_low
-- name    : RawBdd.cook_low
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:58:26.46886+00:00
-- url     : https://prove2.me/theorems/e9fe9ae9-74a3-474c-ab48-a181131f7c83
-- title:
--   Raw Bdd: cook low
-- statement:
--   The Raw Bdd construction uses the cook low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L2129-L2129
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L2129-L2129

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

theorem RawBdd.cook_low {rn : RawNode n} {h1} {h2} : rn.lo.cook (m := m) h1 = (rn.cook h2).low := by sorry
