-- Prove2me | Theorems.Thm_Psi_lead_false_split
-- name    : Psi.lead_false_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:15:55.942034+00:00
-- url     : https://prove2.me/theorems/6911434b-7be9-4a23-bf20-7b78de7f51c3
-- title:
--   Psi: lead false split
-- statement:
--   Leading East-run split.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L51-L54
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L51-L54

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem Psi.lead_false_split (B : List Bool) :
    B = List.replicate ((B.takeWhile (· = false)).length) false ++ B.dropWhile (· = false) := by sorry
