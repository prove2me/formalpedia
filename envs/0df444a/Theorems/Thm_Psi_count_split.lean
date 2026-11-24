-- Prove2me | Theorems.Thm_Psi_count_split
-- name    : Psi.count_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:10:14.287217+00:00
-- url     : https://prove2.me/theorems/36b9402a-0ec8-4847-9550-d029c448d02a
-- title:
--   Psi: count split
-- statement:
--   The Psi construction uses the count split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PhiBasic.lean#L135-L140
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PhiBasic.lean#L135-L140

import Definitions.Def_RequestProject_Psi_PathLemmas
import Definitions.Def_RequestProject_Psi_PhiBasic
set_option autoImplicit true
open Psi

theorem Psi.count_split (p : List Bool) (h : p.head? = some true) :
    numRises p + numValleys p + 1 = numN p := by sorry
