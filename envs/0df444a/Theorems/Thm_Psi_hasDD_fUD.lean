-- Prove2me | Theorems.Thm_Psi_hasDD_fUD
-- name    : Psi.hasDD_fUD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:56:16.12067+00:00
-- url     : https://prove2.me/theorems/f66b6689-cbbc-4f77-9d96-ebe9636a267a
-- title:
--   Psi: has DD f UD
-- statement:
--   The Psi construction uses the has DD f UD property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L241-L246
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L241-L246

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.hasDD_fUD (a : Nat) : hasDD (fUD a) = false := by sorry
