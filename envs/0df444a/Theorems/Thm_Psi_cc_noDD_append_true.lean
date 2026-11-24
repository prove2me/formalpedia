-- Prove2me | Theorems.Thm_Psi_cc_noDD_append_true
-- name    : Psi.cc_noDD_append_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:13:15.498568+00:00
-- url     : https://prove2.me/theorems/f0521296-fe6d-433d-abf8-c001fc1f598f
-- title:
--   Psi: cc no DD append true
-- statement:
--   Contracting `ρ ++ Z` when `ρ` has no `DD` and `Z` starts with a North step:
--   every East step of `ρ` is contracted, leaving `numN ρ` North steps in front of
--   `cc Z`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L252-L264
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L252-L264

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp
set_option autoImplicit true
open Psi

theorem Psi.cc_noDD_append_true (rho Z : List Bool) (hrho : hasDD rho = false)
    (hZ : Z.head? = some true) :
    cc (rho ++ Z) = List.replicate (numN rho) true ++ cc Z := by sorry
