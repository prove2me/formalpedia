-- Prove2me | Theorems.Thm_Psi_desCompAux_noDescent
-- name    : Psi.desCompAux_noDescent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:11:45.884931+00:00
-- url     : https://prove2.me/theorems/082f7437-ef35-4089-9d24-366e3407f7b1
-- title:
--   Psi: des Comp Aux no Descent
-- statement:
--   The Psi construction uses the des Comp Aux no Descent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L410-L423
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L410-L423

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.desCompAux_noDescent (w : List Bool) (hnd : noDescent w = true) (cur : ℕ) :
    desCompAux w cur = [cur + w.length] := by sorry
