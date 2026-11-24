-- Prove2me | Theorems.Thm_Psi_deltaAux_shift
-- name    : Psi.deltaAux_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:11:45.877621+00:00
-- url     : https://prove2.me/theorems/070a01c1-e32a-4de6-8fae-8220a0e15971
-- title:
--   Psi: delta Aux shift
-- statement:
--   The Psi construction uses the delta Aux shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L396-L404
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L396-L404

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.deltaAux_shift (r : List ℕ) (acc : ℕ) :
    deltaAux r acc = (deltaAux r 0).map (· + acc) := by sorry
