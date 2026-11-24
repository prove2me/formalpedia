-- Prove2me | Theorems.Thm_Psi_stEast_getLast_false
-- name    : Psi.stEast_getLast_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:09:36.0287+00:00
-- url     : https://prove2.me/theorems/d10f60d3-3de7-48ab-9a3e-afa6881703c5
-- title:
--   Psi: st East get Last false
-- statement:
--   The Psi construction uses the st East get Last false property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L350-L356
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L350-L356

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.stEast_getLast_false (p : List Bool) (hp : p.getLast? = some false) (x : Bool) :
    stEast p x = true := by sorry
