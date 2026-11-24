-- Prove2me | Theorems.Thm_Psi_runHeight_flatten_UD
-- name    : Psi.runHeight_flatten_UD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:50:43.509453+00:00
-- url     : https://prove2.me/theorems/0ff65c6d-9ded-4a28-acc8-e8e729840ad5
-- title:
--   Psi: run Height flatten UD
-- statement:
--   The Psi construction uses the run Height flatten UD property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L206-L210
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L206-L210

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.runHeight_flatten_UD (l : ℕ) (h : Int) :
    runHeight ((List.replicate l [true, false]).flatten) h = h := by sorry
