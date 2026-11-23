-- Prove2me | Theorems.Thm_RawBdd_RawPointer_cook_eq
-- name    : RawBdd.RawPointer.cook_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:00:51.450137+00:00
-- url     : https://prove2.me/theorems/6bf795e8-088d-4132-84d1-706d4aaaa79d
-- title:
--   Raw Pointer: cook eq
-- statement:
--   `cook` ignores the `Bounded` witness: the bound is a `Prop`, so two cooks of the same
--   raw pointer at the same heap size are equal.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L2095-L2098
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L2095-L2098

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

theorem RawBdd.RawPointer.cook_eq {p : RawPointer} {h1 h2 : p.Bounded m} : p.cook h1 = p.cook h2 := by sorry
