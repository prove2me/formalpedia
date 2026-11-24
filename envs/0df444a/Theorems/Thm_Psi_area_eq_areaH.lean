-- Prove2me | Theorems.Thm_Psi_area_eq_areaH
-- name    : Psi.area_eq_areaH
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:02:23.4528+00:00
-- url     : https://prove2.me/theorems/4d3869c6-bc77-4b1e-a668-122146fab53c
-- title:
--   Psi: area eq area H
-- statement:
--   For a genuine Dyck path the `ℕ`-valued `area` agrees with `areaH`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L87-L90
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L87-L90

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.area_eq_areaH (p : List Bool) (hv : validFrom p 0) :
    (area p : Int) = areaH p 0 false := by sorry
