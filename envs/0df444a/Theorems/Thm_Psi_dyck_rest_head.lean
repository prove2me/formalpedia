-- Prove2me | Theorems.Thm_Psi_dyck_rest_head
-- name    : Psi.dyck_rest_head
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:03:48.86249+00:00
-- url     : https://prove2.me/theorems/ceaa976d-1af6-430b-93e5-5a415bb61f31
-- title:
--   Psi: dyck rest head
-- statement:
--   In the `some` branch (a `DD` exists), the residual path starts with a North step.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L334-L371
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L334-L371

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem Psi.dyck_rest_head (π : List Bool) (i : ℕ) (hd : IsDyck π) (hne : π ≠ [])
    (hsome : firstDDidx (π.drop (2 * cUD π + 1)) = some i) :
    (π.drop (2 * cUD π + 1)).head? = some true := by sorry
