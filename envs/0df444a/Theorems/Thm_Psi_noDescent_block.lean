-- Prove2me | Theorems.Thm_Psi_noDescent_block
-- name    : Psi.noDescent_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:00:24.140931+00:00
-- url     : https://prove2.me/theorems/d8a93395-002e-4092-8ee1-53b463412342
-- title:
--   Psi: no Descent block
-- statement:
--   The Psi construction uses the no Descent block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L573-L579
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L573-L579

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem Psi.noDescent_block (a b : ℕ) (w' : List Bool) (hb : 1 ≤ b) :
    noDescent (List.replicate a false ++ List.replicate b true ++ false :: w') = false := by sorry
