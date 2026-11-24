-- Prove2me | Theorems.Thm_Psi_psi_isValid
-- name    : Psi.psi_isValid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:18:37.500927+00:00
-- url     : https://prove2.me/theorems/778f3a53-ab1b-449e-88b4-943de22b6089
-- title:
--   Psi: psi is Valid
-- statement:
--   Well-definedness (`lem:well-defined`): `Ψ` of a nonempty Dyck path is valid
--   data.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Bijection.lean#L377-L379
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Bijection.lean#L377-L379

import Definitions.Def_RequestProject_Psi_Inverse
import Definitions.Def_RequestProject_Psi_Bijection
set_option autoImplicit true
open Psi

theorem Psi.psi_isValid (π : List Bool) (hd : IsDyck π) (hne : π ≠ []) :
    IsValid (psiPath π).1 (psiPath π).2 := by sorry
