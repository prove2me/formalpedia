-- Prove2me | Theorems.Thm_P2M_Bdd_Ordered_of_terminal__2f4d39cf78e1
-- name    : P2M_Bdd_Ordered_of_terminal__2f4d39cf78e1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:00:11.079342+00:00
-- url     : https://prove2.me/theorems/b967db7c-bde0-420f-8e95-2c237e3fd12d
-- title:
--   P2 M Bdd Ordered of terminal  2f4d39cf78e1: P2 M Bdd Ordered of terminal  2f4d39cf78e1
-- statement:
--   The P2 M Bdd Ordered of terminal  2f4d39cf78e1 construction uses the P2 M Bdd Ordered of terminal  2f4d39cf78e1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L168-L173
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L168-L173

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

theorem P2M_Bdd_Ordered_of_terminal__2f4d39cf78e1 {B : Bdd n m} : B.root = terminal b → B.Ordered := by sorry

alias «Bdd».«Ordered_of_terminal'» := P2M_Bdd_Ordered_of_terminal__2f4d39cf78e1
