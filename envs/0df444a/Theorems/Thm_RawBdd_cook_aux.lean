-- Prove2me | Theorems.Thm_RawBdd_cook_aux
-- name    : RawBdd.cook_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:59:24.238795+00:00
-- url     : https://prove2.me/theorems/52da2254-1730-417a-b72e-74a40548421b
-- title:
--   Raw Bdd: cook aux
-- statement:
--   The Raw Bdd construction uses the cook aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L2137-L2144
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L2137-L2144

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

theorem RawBdd.cook_aux {n : Nat} {j : Fin n} {a : Nat} {hj : (j : Nat) < a} {p : RawPointer} {h1 : p.Bounded n} {h2 : p.Bounded a} : p.cook h1 = .node j → p.cook h2 = .node ⟨j, hj⟩ := by sorry
