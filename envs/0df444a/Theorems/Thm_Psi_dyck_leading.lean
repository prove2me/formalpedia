-- Prove2me | Theorems.Thm_Psi_dyck_leading
-- name    : Psi.dyck_leading
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:55:39.029649+00:00
-- url     : https://prove2.me/theorems/f5666ac7-7970-47b1-9d88-40a4cbaa6d8b
-- title:
--   Psi: dyck leading
-- statement:
--   Leading decomposition: a nonempty Dyck path is `(UD)^a U rest`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L299-L331
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L299-L331

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem Psi.dyck_leading (π : List Bool) (hd : IsDyck π) (hne : π ≠ []) :
    π = (List.replicate (cUD π) [true, false]).flatten ++ true :: π.drop (2 * cUD π + 1) := by sorry
