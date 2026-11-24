-- Prove2me | Theorems.Thm_Psi_cUDraw_fUD_append
-- name    : Psi.cUDraw_fUD_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:57:19.0318+00:00
-- url     : https://prove2.me/theorems/36d354d7-a23c-4072-a262-740951f08188
-- title:
--   Psi: c UDraw f UD append
-- statement:
--   `cUDraw` is additive over a leading `(UD)^a` block.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L88-L95
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L88-L95

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward
set_option autoImplicit true
open Psi

theorem Psi.cUDraw_fUD_append (a : ℕ) (t : List Bool) :
    cUDraw ((List.replicate a [true, false]).flatten ++ t) = a + cUDraw t := by sorry
