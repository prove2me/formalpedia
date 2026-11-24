-- Prove2me | Theorems.Thm_Psi_phi_psi
-- name    : Psi.phi_psi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:04:21.885004+00:00
-- url     : https://prove2.me/theorems/ef0d3532-fc5a-4f42-b9a3-5b5ff6692d6b
-- title:
--   Psi: phi psi
-- statement:
--   Round-trip `Φ ∘ Ψ = id` on nonempty Dyck paths (the surjectivity content).
--   The empty path is excluded: `Φ` always produces a nonempty path.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L675-L690
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L675-L690

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem Psi.phi_psi (π : List Bool) (h : IsDyck π) (hne : π ≠ []) :
    phiPath (psiPath π).1 (psiPath π).2 = π := by sorry
