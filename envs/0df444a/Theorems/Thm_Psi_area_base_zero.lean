-- Prove2me | Theorems.Thm_Psi_area_base_zero
-- name    : Psi.area_base_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:12:17.929192+00:00
-- url     : https://prove2.me/theorems/ec9464d4-dd5d-453c-94d1-67b4f5b007fb
-- title:
--   Psi: area base zero
-- statement:
--   `ℕ`-level: the base path has area `0`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L717-L729
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L717-L729

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.area_base_zero (l k : ℕ) :
    area ((List.replicate l [true, false]).flatten ++ List.replicate (k + 1) true
      ++ List.replicate (k + 1) false) = 0 := by sorry
