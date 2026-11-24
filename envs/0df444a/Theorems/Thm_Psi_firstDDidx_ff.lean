-- Prove2me | Theorems.Thm_Psi_firstDDidx_ff
-- name    : Psi.firstDDidx_ff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:59:39.059204+00:00
-- url     : https://prove2.me/theorems/e3caaf0a-d2ec-43d5-8c6f-5a2cea7aaa91
-- title:
--   Psi: first DDidx ff
-- statement:
--   `firstDDidx` finds a `DD` at position `0`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L137-L137
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L137-L137

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward
set_option autoImplicit true
open Psi

theorem Psi.firstDDidx_ff (r : List Bool) : firstDDidx (false :: false :: r) = some 0 := by sorry
