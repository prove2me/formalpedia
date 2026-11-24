-- Prove2me | Theorems.Thm_Psi_validFrom_replicate_false
-- name    : Psi.validFrom_replicate_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:01:06.193467+00:00
-- url     : https://prove2.me/theorems/502c0749-f25f-4f1e-9be0-7154b6fc0038
-- title:
--   Psi: valid From replicate false
-- statement:
--   The Psi construction uses the valid From replicate false property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L174-L180
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L174-L180

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.validFrom_replicate_false (n : ℕ) (h : Int) (hh : (n : Int) ≤ h) :
    validFrom (List.replicate n false) h := by sorry
