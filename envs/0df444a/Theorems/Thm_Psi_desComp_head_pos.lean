-- Prove2me | Theorems.Thm_Psi_desComp_head_pos
-- name    : Psi.desComp_head_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:12:31.625935+00:00
-- url     : https://prove2.me/theorems/cd9b26fc-b998-4ae0-9223-b9352d5c4cd9
-- title:
--   Psi: des Comp head pos
-- statement:
--   The Psi construction uses the des Comp head pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L50-L65
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L50-L65

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp
set_option autoImplicit true
open Psi

theorem Psi.desComp_head_pos (word : List Bool) (hw : word ≠ []) :
    0 < (desComp word).headD 0 := by sorry
