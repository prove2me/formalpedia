-- Prove2me | Theorems.Thm_Pointer_equiv_symm
-- name    : Pointer.equiv_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:57:49.58228+00:00
-- url     : https://prove2.me/theorems/27e9620c-6977-435b-acd8-2ab03ea079c7
-- title:
--   Pointer: equiv symm
-- statement:
--   The Pointer construction uses the equiv symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1849-L1885
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1849-L1885

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

theorem Pointer.equiv_symm {p : Pointer m} : p.equiv q → q.equiv p := by sorry
