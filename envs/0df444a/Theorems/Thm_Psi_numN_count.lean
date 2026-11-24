-- Prove2me | Theorems.Thm_Psi_numN_count
-- name    : Psi.numN_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:10:09.861633+00:00
-- url     : https://prove2.me/theorems/bd6cebf0-1093-4f35-a2d1-e727ecbde0bc
-- title:
--   Psi: num N count
-- statement:
--   The Psi construction uses the num N count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PhiBasic.lean#L119-L134
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PhiBasic.lean#L119-L134

import Definitions.Def_RequestProject_Psi_PathLemmas
import Definitions.Def_RequestProject_Psi_PhiBasic
set_option autoImplicit true
open Psi

theorem Psi.numN_count (p : List Bool) (le sn : Bool) :
    numN p = countRises p le sn + countValleys p le
      + (if le = false ∧ sn = false ∧ p.head? = some true then 1 else 0) := by sorry
