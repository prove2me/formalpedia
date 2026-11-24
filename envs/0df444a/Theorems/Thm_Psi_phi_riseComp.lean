-- Prove2me | Theorems.Thm_Psi_phi_riseComp
-- name    : Psi.phi_riseComp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:39:28.220911+00:00
-- url     : https://prove2.me/theorems/e7f1f2aa-c1cb-4ebe-9e1a-9a67bae3e4c0
-- title:
--   Psi: phi rise Comp
-- statement:
--   Rise-composition preservation (`lem:comp`): `μ(c(π)) = μ(τ)`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L325-L396
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L325-L396

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp
set_option autoImplicit true
open Psi

theorem Psi.phi_riseComp (w : List Bool) (av : List ℕ) (h : IsValid w av) :
    northRuns (cc (phiPath w av)) = muVec (tauOf w av) := by sorry
