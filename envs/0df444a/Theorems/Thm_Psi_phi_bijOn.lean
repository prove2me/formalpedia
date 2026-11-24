-- Prove2me | Theorems.Thm_Psi_phi_bijOn
-- name    : Psi.phi_bijOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:49:33.576182+00:00
-- url     : https://prove2.me/theorems/51fbc5e6-b356-4728-88a4-b5e74585ab0b
-- title:
--   Psi: phi bij On
-- statement:
--   **The bijection** (`the main theorem`): `Φ = phiPath` is a bijection between
--   valid data of size `n` and decorated Dyck paths of size `n`, with explicit
--   inverse `Ψ = psiPath`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Bijection.lean#L396-L403
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Bijection.lean#L396-L403

import Definitions.Def_RequestProject_Psi_Inverse
import Definitions.Def_RequestProject_Psi_Bijection
set_option autoImplicit true
open Psi

theorem Psi.phi_bijOn (n : ℕ) (hn : 1 ≤ n) :
    Set.BijOn (fun p : List Bool × List ℕ => phiPath p.1 p.2) (Dom n) (Cod n) := by sorry
