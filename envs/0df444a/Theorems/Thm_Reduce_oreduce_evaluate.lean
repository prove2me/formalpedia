-- Prove2me | Theorems.Thm_Reduce_oreduce_evaluate
-- name    : Reduce.oreduce_evaluate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:15:36.380817+00:00
-- url     : https://prove2.me/theorems/6dc44f36-3681-43ef-afc8-2d068d0b1535
-- title:
--   Reduce: oreduce evaluate
-- statement:
--   The Reduce construction uses the oreduce evaluate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/Main.lean#L234-L235
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/Main.lean#L234-L235

import Definitions.Def_Bdd_Reduce_Process
import Definitions.Def_Bdd_Reduce_Discover
import Definitions.Def_Bdd_Reduce_Main
set_option autoImplicit true
open Pointer
open Bdd
open RawBdd
open Reduce

theorem Reduce.oreduce_evaluate {O : OBdd n m} : (oreduce O).1.2.evaluate = O.evaluate := by sorry
