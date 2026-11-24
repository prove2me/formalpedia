-- Prove2me | Theorems.Thm_Psi_hasDD_prefix
-- name    : Psi.hasDD_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:02:45.195524+00:00
-- url     : https://prove2.me/theorems/90a250b1-15f4-4fb8-a855-b601e3896ae9
-- title:
--   Psi: has DD prefix
-- statement:
--   A prefix of a path with no `DD` has no `DD`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L185-L197
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L185-L197

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.hasDD_prefix (s t : List Bool) (h : hasDD (s ++ t) = false) : hasDD s = false := by sorry
