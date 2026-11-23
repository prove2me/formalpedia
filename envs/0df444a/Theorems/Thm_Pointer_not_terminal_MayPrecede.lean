-- Prove2me | Theorems.Thm_Pointer_not_terminal_MayPrecede
-- name    : Pointer.not_terminal_MayPrecede
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:58:42.026931+00:00
-- url     : https://prove2.me/theorems/33955637-9ed3-40b2-9f53-de8045859c8b
-- title:
--   Pointer: not terminal May Precede
-- statement:
--   Terminals must not precede other pointers.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L123-L126
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L123-L126

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

theorem Pointer.not_terminal_MayPrecede : ¬ MayPrecede M (terminal b) p := by sorry
