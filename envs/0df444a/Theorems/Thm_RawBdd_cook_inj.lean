-- Prove2me | Theorems.Thm_RawBdd_cook_inj
-- name    : RawBdd.cook_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:57:53.048128+00:00
-- url     : https://prove2.me/theorems/bf5bff11-31d3-4eae-9320-61131e0ccc0d
-- title:
--   Raw Bdd: cook inj
-- statement:
--   The Raw Bdd construction uses the cook inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L2133-L2135
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L2133-L2135

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

theorem RawBdd.cook_inj {p q : RawPointer} {hp} {hq} : p.cook (m := m) hp = q.cook hq → p = q := by sorry
