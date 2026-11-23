-- Prove2me | Theorems.Thm_P2M_OBdd_evaluate_terminal__321343d95937
-- name    : P2M_OBdd_evaluate_terminal__321343d95937
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:55:12.940734+00:00
-- url     : https://prove2.me/theorems/39cc38a1-8202-4436-ae03-8397e3c8c872
-- title:
--   P2 M OBdd evaluate terminal  321343d95937: P2 M OBdd evaluate terminal  321343d95937
-- statement:
--   The P2 M OBdd evaluate terminal  321343d95937 construction uses the P2 M OBdd evaluate terminal  321343d95937 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L655-L658
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L655-L658

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

theorem P2M_OBdd_evaluate_terminal__321343d95937 {n m} {O : OBdd n m} : O.1.root = terminal b → O.evaluate = Function.const _ b := by sorry

alias «OBdd».«evaluate_terminal'» := P2M_OBdd_evaluate_terminal__321343d95937
