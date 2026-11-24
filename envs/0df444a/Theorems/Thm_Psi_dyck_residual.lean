-- Prove2me | Theorems.Thm_Psi_dyck_residual
-- name    : Psi.dyck_residual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:04:07.098533+00:00
-- url     : https://prove2.me/theorems/3a8716eb-17f2-4228-9fdc-a24cb0fa9e11
-- title:
--   Psi: dyck residual
-- statement:
--   The residual `ρ ++ ρ'` (path with the pyramid removed) is again a Dyck path.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L511-L550
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L511-L550

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem Psi.dyck_residual (π : List Bool) (b : ℕ) (ρ ρ' : List Bool)
    (hd : IsDyck π) (hne : π ≠ [])
    (hstruct : π.drop (2 * cUD π + 1)
      = ρ ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ')
    (hρDD : hasDD ρ = false) (hρU : ρ = [] ∨ ρ.head? = some true) :
    IsDyck (ρ ++ ρ') := by sorry
