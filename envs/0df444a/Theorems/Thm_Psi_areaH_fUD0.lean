-- Prove2me | Theorems.Thm_Psi_areaH_fUD0
-- name    : Psi.areaH_fUD0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:02:49.189149+00:00
-- url     : https://prove2.me/theorems/da734e4f-bd76-4e03-afe8-a9ef3c80dd64
-- title:
--   Psi: area H f UD0
-- statement:
--   The Psi construction uses the area H f UD0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L110-L117
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L110-L117

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.areaH_fUD0 (a : Nat) (le : Bool) : areaH (fUD a) 0 le = 0 := by sorry
