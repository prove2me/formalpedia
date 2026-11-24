-- Prove2me | Theorems.Thm_Psi_hasDD_replicate_true
-- name    : Psi.hasDD_replicate_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:56:15.850823+00:00
-- url     : https://prove2.me/theorems/34874acc-6137-4fac-acef-94d2868d9bfc
-- title:
--   Psi: has DD replicate true
-- statement:
--   The Psi construction uses the has DD replicate true property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L231-L234
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L231-L234

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.hasDD_replicate_true (n : Nat) : hasDD (List.replicate n true) = false := by sorry
