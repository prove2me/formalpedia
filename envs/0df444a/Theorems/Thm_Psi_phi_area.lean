-- Prove2me | Theorems.Thm_Psi_phi_area
-- name    : Psi.phi_area
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:36:46.868052+00:00
-- url     : https://prove2.me/theorems/114ed91a-91f7-498e-8fb9-5dec3ab4a870
-- title:
--   Psi: phi area
-- statement:
--   Area preservation (`lem:area`): `area(π) = area(τ) = Σ av`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L757-L801
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L757-L801

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.phi_area (w : List Bool) (av : List ℕ) (h : IsValid w av) :
    area (phiPath w av) = av.sum := by sorry
