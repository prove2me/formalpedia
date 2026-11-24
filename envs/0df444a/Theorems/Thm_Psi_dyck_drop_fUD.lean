-- Prove2me | Theorems.Thm_Psi_dyck_drop_fUD
-- name    : Psi.dyck_drop_fUD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:16:49.825587+00:00
-- url     : https://prove2.me/theorems/43a6b215-cd86-4ea0-aa06-f1e9feb9fc14
-- title:
--   Psi: dyck drop f UD
-- statement:
--   The Psi construction uses the dyck drop f UD property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L288-L296
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L288-L296

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem Psi.dyck_drop_fUD (π : List Bool) (hd : IsDyck π) : IsDyck (π.drop (2 * cUDraw π)) := by sorry
