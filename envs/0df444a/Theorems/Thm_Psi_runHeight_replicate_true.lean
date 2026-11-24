-- Prove2me | Theorems.Thm_Psi_runHeight_replicate_true
-- name    : Psi.runHeight_replicate_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:54:49.784575+00:00
-- url     : https://prove2.me/theorems/d84609d3-c143-4a9d-ab87-188048ca5472
-- title:
--   Psi: run Height replicate true
-- statement:
--   The Psi construction uses the run Height replicate true property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L156-L160
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L156-L160

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.runHeight_replicate_true (n : ℕ) (h : Int) :
    runHeight (List.replicate n true) h = h + n := by sorry
