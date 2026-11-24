-- Prove2me | Theorems.Thm_Psi_numNBeforeDD_fUD
-- name    : Psi.numNBeforeDD_fUD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:17:42.874832+00:00
-- url     : https://prove2.me/theorems/e388a68a-086f-4a0e-a3ac-3fe136ac421d
-- title:
--   Psi: num NBefore DD f UD
-- statement:
--   `(UD)^m` is `DD`-free with `m` North steps.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Bijection.lean#L95-L116
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Bijection.lean#L95-L116

import Definitions.Def_RequestProject_Psi_Inverse
import Definitions.Def_RequestProject_Psi_Bijection
set_option autoImplicit true
open Psi

theorem Psi.numNBeforeDD_fUD (m : ℕ) :
    numNBeforeDD ((List.replicate m [true, false]).flatten) = m := by sorry
