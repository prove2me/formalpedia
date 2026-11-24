-- Prove2me | Theorems.Thm_Psi_area_reconstruct
-- name    : Psi.area_reconstruct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:11:46.444818+00:00
-- url     : https://prove2.me/theorems/55bd58ef-f8e6-43b3-a28c-d28c005b48ed
-- title:
--   Psi: area reconstruct
-- statement:
--   The area identity underlying `lem:area`: inserting the block
--   `(UD)^a U · ρ · U^b D^{b+1}` around the split `π = ρ ρ'` raises the area by
--   exactly `h = #North(ρ)`. Stated over `ℤ` via `areaH`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L333-L392
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L333-L392

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.area_reconstruct (a b : ℕ) (rho rho' : List Bool) (hb : 1 ≤ b)
    (hnoDD : hasDD rho = false)
    (hbd : stEast rho false = false → rho'.head? = some true) :
    areaH ((List.replicate a [true, false]).flatten ++ [true] ++ rho
        ++ List.replicate b true ++ List.replicate (b + 1) false ++ rho') 0 false
      = (numN rho : Int) + areaH (rho ++ rho') 0 false := by sorry
