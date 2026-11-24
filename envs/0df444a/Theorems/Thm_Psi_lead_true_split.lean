-- Prove2me | Theorems.Thm_Psi_lead_true_split
-- name    : Psi.lead_true_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:15:49.979797+00:00
-- url     : https://prove2.me/theorems/6cb34278-1f67-4e63-a53a-158e1449f4fb
-- title:
--   Psi: lead true split
-- statement:
--   Leading North-run split.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L46-L48
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L46-L48

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem Psi.lead_true_split (C : List Bool) :
    C = List.replicate ((C.takeWhile id).length) true ++ C.dropWhile id := by sorry
