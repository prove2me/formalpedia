-- Prove2me | Theorems.Thm_Psi_firstDDidx_false_headtrue
-- name    : Psi.firstDDidx_false_headtrue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:14:07.500803+00:00
-- url     : https://prove2.me/theorems/81d32512-79e0-4205-a394-e8d6df4201da
-- title:
--   Psi: first DDidx false headtrue
-- statement:
--   `firstDDidx (E :: L)` shifts when `L` starts with a North step.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L144-L148
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L144-L148

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward
set_option autoImplicit true
open Psi

theorem Psi.firstDDidx_false_headtrue (L : List Bool) (h : L.head? = some true) :
    firstDDidx (false :: L) = (firstDDidx L).map (· + 1) := by sorry
