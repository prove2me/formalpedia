-- Prove2me | Theorems.Thm_Reduce_oreduce_reduced
-- name    : Reduce.oreduce_reduced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:15:30.455085+00:00
-- url     : https://prove2.me/theorems/bb8700f5-8eec-4e0b-8aa5-c29cd71fdec3
-- title:
--   Reduce: oreduce reduced
-- statement:
--   The Reduce construction uses the oreduce reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/Main.lean#L231-L231
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/Main.lean#L231-L231

import Definitions.Def_Bdd_Reduce_Process
import Definitions.Def_Bdd_Reduce_Discover
import Definitions.Def_Bdd_Reduce_Main
set_option autoImplicit true
open Pointer
open Bdd
open RawBdd
open Reduce

theorem Reduce.oreduce_reduced {O : OBdd n m} : OBdd.Reduced (oreduce O).1.2 := by sorry
