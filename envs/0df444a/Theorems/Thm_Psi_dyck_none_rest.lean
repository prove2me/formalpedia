-- Prove2me | Theorems.Thm_Psi_dyck_none_rest
-- name    : Psi.dyck_none_rest
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:03:49.831015+00:00
-- url     : https://prove2.me/theorems/9b32e642-7e54-4a48-b8d8-bc9a651b3ac3
-- title:
--   Psi: dyck none rest
-- statement:
--   In the `none` branch (no `DD`), the residual path is a single East step, so
--   `π = (UD)^a U D`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L445-L485
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L445-L485

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem Psi.dyck_none_rest (π : List Bool) (hd : IsDyck π) (hne : π ≠ [])
    (hnone : firstDDidx (π.drop (2 * cUD π + 1)) = none) :
    π.drop (2 * cUD π + 1) = [false] := by sorry
