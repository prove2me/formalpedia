-- Prove2me | Theorems.Thm_Psi_phi_mapsTo
-- name    : Psi.phi_mapsTo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:13:50.050775+00:00
-- url     : https://prove2.me/theorems/3d9de46e-2cd7-4071-be26-62dec39e8cdd
-- title:
--   Psi: phi maps To
-- statement:
--   `Φ` maps the domain into the codomain: every reconstructed path from a valid
--   datum of "size `n`" is a Dyck path of size `n`.  This is the `MapsTo` part of the
--   bijectivity statement, and follows from `phi_isDyck` and `phi_size`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L18-L22
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L18-L22

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward
set_option autoImplicit true
open Psi

theorem Psi.phi_mapsTo (n : ℕ) :
    Set.MapsTo (fun p : List Bool × List ℕ => phiPath p.1 p.2) (Dom n) (Cod n) := by sorry
