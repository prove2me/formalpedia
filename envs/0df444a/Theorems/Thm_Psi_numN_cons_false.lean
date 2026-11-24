-- Prove2me | Theorems.Thm_Psi_numN_cons_false
-- name    : Psi.numN_cons_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:52:57.050447+00:00
-- url     : https://prove2.me/theorems/74833798-28b4-4195-a184-096e95cd9ae2
-- title:
--   Psi: num N cons false
-- statement:
--   The Psi construction uses the num N cons false property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L22-L23
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L22-L23

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.numN_cons_false (t : List Bool) : numN (false :: t) = numN t := by sorry
