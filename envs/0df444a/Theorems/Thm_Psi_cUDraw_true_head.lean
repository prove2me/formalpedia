-- Prove2me | Theorems.Thm_Psi_cUDraw_true_head
-- name    : Psi.cUDraw_true_head
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:13:43.098672+00:00
-- url     : https://prove2.me/theorems/616ff31c-402d-4d87-aefb-ecc45178424a
-- title:
--   Psi: c UDraw true head
-- statement:
--   `cUDraw` of `U :: L` is `0` when `L` starts with a North step.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L98-L102
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L98-L102

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward
set_option autoImplicit true
open Psi

theorem Psi.cUDraw_true_head (L : List Bool) (h : L.head? = some true) :
    cUDraw (true :: L) = 0 := by sorry
