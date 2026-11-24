-- Prove2me | Theorems.Thm_Psi_cc_noDD_append_gen
-- name    : Psi.cc_noDD_append_gen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:03:14.884039+00:00
-- url     : https://prove2.me/theorems/802a3604-1b1e-4321-8a0d-47ecff618919
-- title:
--   Psi: cc no DD append gen
-- statement:
--   Contracting `ρ ++ Z` when `ρ` has no `DD`: all of `ρ`'s East steps are
--   contracted, contributing `numN ρ` North steps; a trailing East step of `ρ` is
--   folded into `Z` as a leading `false`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L182-L212
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L182-L212

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp
set_option autoImplicit true
open Psi

theorem Psi.cc_noDD_append_gen (rho Z : List Bool) (hrho : hasDD rho = false) :
    cc (rho ++ Z)
      = List.replicate (numN rho) true ++ (if stEast rho false then cc (false :: Z) else cc Z) := by sorry
