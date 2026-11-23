-- Prove2me | Theorems.Thm_P2M_Pointer_toVar_heap_set__d9257dfabaf5
-- name    : P2M_Pointer_toVar_heap_set__d9257dfabaf5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:59:54.20088+00:00
-- url     : https://prove2.me/theorems/72117d79-db27-439c-b3c6-48597a6e73df
-- title:
--   P2 M Pointer to Var heap set  d9257dfabaf5: P2 M Pointer to Var heap set  d9257dfabaf5
-- statement:
--   The P2 M Pointer to Var heap set  d9257dfabaf5 construction uses the P2 M Pointer to Var heap set  d9257dfabaf5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L113-L117
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L113-L117

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

theorem P2M_Pointer_toVar_heap_set__d9257dfabaf5 {i j : Fin n} : i ≠ j → (toVar (M.set i N) (node j)) = (toVar M (node j)) := by sorry

alias «Pointer».«toVar_heap_set'» := P2M_Pointer_toVar_heap_set__d9257dfabaf5
