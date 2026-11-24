-- Prove2me | Theorems.Thm_Psi_area_sandwich
-- name    : Psi.area_sandwich
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:12:23.697323+00:00
-- url     : https://prove2.me/theorems/2af715a7-eb1c-4826-9ded-067e38f6bf70
-- title:
--   Psi: area sandwich
-- statement:
--   `ℕ`-level area identity for the reconstruction block.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L732-L754
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L732-L754

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.area_sandwich (a b : ℕ) (rho rho' : List Bool) (hb : 1 ≤ b)
    (hnoDD : hasDD rho = false)
    (hbd : stEast rho false = false → rho'.head? = some true)
    (hpi : IsDyck (rho ++ rho')) :
    area ((List.replicate a [true, false]).flatten ++ [true] ++ rho
      ++ List.replicate b true ++ List.replicate (b + 1) false ++ rho')
      = numN rho + area (rho ++ rho') := by sorry
