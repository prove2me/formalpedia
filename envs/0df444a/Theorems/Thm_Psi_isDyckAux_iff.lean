-- Prove2me | Theorems.Thm_Psi_isDyckAux_iff
-- name    : Psi.isDyckAux_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:50:47.336801+00:00
-- url     : https://prove2.me/theorems/2d7330af-86eb-4c1b-ab9c-11af5acc78a9
-- title:
--   Psi: is Dyck Aux iff
-- statement:
--   The Psi construction uses the is Dyck Aux iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L150-L154
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L150-L154

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.isDyckAux_iff (p : List Bool) (h : Int) :
    IsDyckAux p h ↔ validFrom p h ∧ runHeight p h = 0 := by sorry
