-- Prove2me | Theorems.Thm_Psi_runHeight_eq
-- name    : Psi.runHeight_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:10:26.736815+00:00
-- url     : https://prove2.me/theorems/e3c95cc0-024e-4bd2-87a5-124f0b1b572e
-- title:
--   Psi: run Height eq
-- statement:
--   `runHeight p h = h + #North(p) - #East(p)`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L26-L33
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L26-L33

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.runHeight_eq (p : List Bool) (h : Int) :
    runHeight p h = h + numN p - numE p := by sorry
