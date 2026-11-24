-- Prove2me | Theorems.Thm_Psi_runHeight_replicate_false
-- name    : Psi.runHeight_replicate_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:55:06.469004+00:00
-- url     : https://prove2.me/theorems/9c9e1e8d-d11e-463c-8895-03d994ebcdca
-- title:
--   Psi: run Height replicate false
-- statement:
--   The Psi construction uses the run Height replicate false property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L162-L166
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L162-L166

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.runHeight_replicate_false (n : ℕ) (h : Int) :
    runHeight (List.replicate n false) h = h - n := by sorry
