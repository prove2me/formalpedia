-- Prove2me | Theorems.Thm_Psi_desComp_noDescent
-- name    : Psi.desComp_noDescent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:53:07.763801+00:00
-- url     : https://prove2.me/theorems/0ba22736-67d6-41a0-b3ee-c34f68f9cb27
-- title:
--   Psi: des Comp no Descent
-- statement:
--   Base descent composition: for a weakly increasing `w`, `Des(0w) = [|w|+1]`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L461-L465
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L461-L465

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.desComp_noDescent {w : List Bool} (hnd : noDescent w = true) :
    desComp (false :: w) = [w.length + 1] := by sorry
