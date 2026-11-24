-- Prove2me | Theorems.Thm_Psi_deltaOf_length
-- name    : Psi.deltaOf_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:58:17.926257+00:00
-- url     : https://prove2.me/theorems/ce4f4e95-a8d9-4b39-9769-1b1d4dba6484
-- title:
--   Psi: delta Of length
-- statement:
--   The Psi construction uses the delta Of length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L495-L495
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L495-L495

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.deltaOf_length (γ : List ℕ) : (deltaOf γ).length = γ.length := by sorry
