-- Prove2me | Theorems.Thm_Psi_numN_single_true
-- name    : Psi.numN_single_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:02:14.857794+00:00
-- url     : https://prove2.me/theorems/1647e2a0-f7ef-4a60-b2e5-d4d1c3074f3a
-- title:
--   Psi: num N single true
-- statement:
--   The Psi construction uses the num N single true property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PhiBasic.lean#L113-L113
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PhiBasic.lean#L113-L113

import Definitions.Def_RequestProject_Psi_PathLemmas
import Definitions.Def_RequestProject_Psi_PhiBasic
set_option autoImplicit true
open Psi

theorem Psi.numN_single_true : numN [true] = 1 := by sorry
