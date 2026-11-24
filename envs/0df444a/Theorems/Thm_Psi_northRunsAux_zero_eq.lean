-- Prove2me | Theorems.Thm_Psi_northRunsAux_zero_eq
-- name    : Psi.northRunsAux_zero_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:12:50.272161+00:00
-- url     : https://prove2.me/theorems/b468ef83-5170-4bd4-872c-055ff20811fa
-- title:
--   Psi: north Runs Aux zero eq
-- statement:
--   The Psi construction uses the north Runs Aux zero eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L124-L144
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L124-L144

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp
set_option autoImplicit true
open Psi

theorem Psi.northRunsAux_zero_eq (J : List Bool) (hpt : ℕ) :
    northRunsAux J 0
      = ppart ((northRunsAux J hpt).headD 0 - hpt) ++ (northRunsAux J hpt).tail := by sorry
