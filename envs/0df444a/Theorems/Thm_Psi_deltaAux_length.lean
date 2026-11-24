-- Prove2me | Theorems.Thm_Psi_deltaAux_length
-- name    : Psi.deltaAux_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:11:51.662807+00:00
-- url     : https://prove2.me/theorems/80545b8d-f5ff-48fb-8961-7823d2c12c60
-- title:
--   Psi: delta Aux length
-- statement:
--   The Psi construction uses the delta Aux length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L490-L493
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L490-L493

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.deltaAux_length (γ : List ℕ) (acc : ℕ) : (deltaAux γ acc).length = γ.length := by sorry
