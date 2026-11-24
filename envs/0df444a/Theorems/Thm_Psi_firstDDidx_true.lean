-- Prove2me | Theorems.Thm_Psi_firstDDidx_true
-- name    : Psi.firstDDidx_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:57:08.714041+00:00
-- url     : https://prove2.me/theorems/536dce3e-d65d-48b3-a752-a008392669a5
-- title:
--   Psi: first DDidx true
-- statement:
--   `firstDDidx` on a North step just shifts.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L133-L134
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L133-L134

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward
set_option autoImplicit true
open Psi

theorem Psi.firstDDidx_true (r : List Bool) :
    firstDDidx (true :: r) = (firstDDidx r).map (· + 1) := by sorry
