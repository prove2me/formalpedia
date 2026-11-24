-- Prove2me | Theorems.Thm_Psi_desCompAux_zeros
-- name    : Psi.desCompAux_zeros
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:11:52.27425+00:00
-- url     : https://prove2.me/theorems/d9560dff-2c12-4011-b4bf-430a904cca0e
-- title:
--   Psi: des Comp Aux zeros
-- statement:
--   The Psi construction uses the des Comp Aux zeros property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L425-L439
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L425-L439

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.desCompAux_zeros (a : ℕ) (rest : List Bool) (cur : ℕ) :
    desCompAux (List.replicate a false ++ (true :: rest)) cur
      = desCompAux (true :: rest) (cur + a) := by sorry
