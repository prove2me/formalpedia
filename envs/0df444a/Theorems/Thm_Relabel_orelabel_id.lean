-- Prove2me | Theorems.Thm_Relabel_orelabel_id
-- name    : Relabel.orelabel_id
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:01:06.631966+00:00
-- url     : https://prove2.me/theorems/f9fa501b-2750-4d32-b9dd-787e8f3ed6e3
-- title:
--   Relabel: orelabel id
-- statement:
--   The Relabel construction uses the orelabel id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Relabel.lean#L430-L430
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Relabel.lean#L430-L430

import Definitions.Def_Bdd_Basic
import Definitions.Def_Bdd_Relabel
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const


set_option autoImplicit true
attribute [local implicit_reducible] OBdd Bdd.Ordered Bdd.RelevantMayPrecede
open Relabel
attribute [local implicit_reducible] relabel relabel_heap relabel_node
attribute [local implicit_reducible] orelabel

theorem Relabel.orelabel_id {O : OBdd n m} : orelabel O (f := id) (by simp) (fun _ _ _ _ _ ↦ by simpa) = O := by sorry
