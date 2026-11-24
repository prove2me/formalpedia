-- Prove2me | Theorems.Thm_Psi_numNBeforeDD_cons_true
-- name    : Psi.numNBeforeDD_cons_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:04:28.658392+00:00
-- url     : https://prove2.me/theorems/4623ddf8-89cc-4f5d-b59d-8c8f88512e3b
-- title:
--   Psi: num NBefore DD cons true
-- statement:
--   The Psi construction uses the num NBefore DD cons true property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Bijection.lean#L22-L23
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Bijection.lean#L22-L23

import Definitions.Def_RequestProject_Psi_Inverse
import Definitions.Def_RequestProject_Psi_Bijection
set_option autoImplicit true
open Psi

theorem Psi.numNBeforeDD_cons_true (r : List Bool) :
    numNBeforeDD (true :: r) = numNBeforeDD r + 1 := by sorry
