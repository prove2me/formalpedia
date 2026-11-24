-- Prove2me | Theorems.Thm_Psi_firstDDidx_drop_ff
-- name    : Psi.firstDDidx_drop_ff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:16:15.745494+00:00
-- url     : https://prove2.me/theorems/84db81ca-a932-478c-8188-9f7ff5acfee0
-- title:
--   Psi: first DDidx drop ff
-- statement:
--   The path drops to two consecutive East steps at the `DD`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L107-L117
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L107-L117

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem Psi.firstDDidx_drop_ff (rest : List Bool) (i : ℕ) (h : firstDDidx rest = some i) :
    ∃ r, rest.drop i = false :: false :: r := by sorry
