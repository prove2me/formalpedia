-- Prove2me | Theorems.Thm_Psi_firstDDidx_prev_true
-- name    : Psi.firstDDidx_prev_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:16:28.612841+00:00
-- url     : https://prove2.me/theorems/357ef3cd-a033-4724-8258-78c2c3cd79e4
-- title:
--   Psi: first DDidx prev true
-- statement:
--   The step just before the first `DD` is a North step.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L142-L169
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L142-L169

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem Psi.firstDDidx_prev_true (rest : List Bool) (i : ℕ) (h : firstDDidx rest = some i) (hi : 1 ≤ i) :
    (rest.take i).getLast? = some true := by sorry
