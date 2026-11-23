-- Prove2me | Theorems.Thm_Pointer_toVar_heap_set
-- name    : Pointer.toVar_heap_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:59:53.081357+00:00
-- url     : https://prove2.me/theorems/352ffd12-8c5d-440a-bae0-da6c1dbf5d13
-- title:
--   Pointer: to Var heap set
-- statement:
--   The Pointer construction uses the to Var heap set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L104-L111
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L104-L111

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

theorem Pointer.toVar_heap_set {i j : Fin n} : i ≠ j → (toVar (M.set i N) (node j)).1 = (toVar M (node j)).1 := by sorry
