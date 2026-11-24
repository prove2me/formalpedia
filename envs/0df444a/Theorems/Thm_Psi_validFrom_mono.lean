-- Prove2me | Theorems.Thm_Psi_validFrom_mono
-- name    : Psi.validFrom_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:08:16.26375+00:00
-- url     : https://prove2.me/theorems/f5a97426-60d1-4e66-b8cc-dcd0a33ba100
-- title:
--   Psi: valid From mono
-- statement:
--   The Psi construction uses the valid From mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L190-L196
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L190-L196

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.validFrom_mono (p : List Bool) (h h' : Int) (hle : h ≤ h')
    (hv : validFrom p h) : validFrom p h' := by sorry
