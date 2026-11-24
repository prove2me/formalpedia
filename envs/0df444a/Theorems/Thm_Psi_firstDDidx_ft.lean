-- Prove2me | Theorems.Thm_Psi_firstDDidx_ft
-- name    : Psi.firstDDidx_ft
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:58:52.825926+00:00
-- url     : https://prove2.me/theorems/fb8e06da-7968-4037-be50-5e2741ce8a8a
-- title:
--   Psi: first DDidx ft
-- statement:
--   `firstDDidx` on `E U ...` shifts.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L140-L141
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L140-L141

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward
set_option autoImplicit true
open Psi

theorem Psi.firstDDidx_ft (r : List Bool) :
    firstDDidx (false :: true :: r) = (firstDDidx (true :: r)).map (· + 1) := by sorry
