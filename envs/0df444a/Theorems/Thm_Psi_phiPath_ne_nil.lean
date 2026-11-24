-- Prove2me | Theorems.Thm_Psi_phiPath_ne_nil
-- name    : Psi.phiPath_ne_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:54:31.109723+00:00
-- url     : https://prove2.me/theorems/786a0f2d-a53f-4dea-8cc6-169d937ce432
-- title:
--   Psi: phi Path ne nil
-- statement:
--   The Psi construction uses the phi Path ne nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L415-L418
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L415-L418

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.phiPath_ne_nil (w : List Bool) (av : List ℕ) : phiPath w av ≠ [] := by sorry
