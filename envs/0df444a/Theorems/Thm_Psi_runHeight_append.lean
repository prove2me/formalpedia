-- Prove2me | Theorems.Thm_Psi_runHeight_append
-- name    : Psi.runHeight_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:50:33.834645+00:00
-- url     : https://prove2.me/theorems/49391e91-d514-42de-af80-e75b2af846a9
-- title:
--   Psi: run Height append
-- statement:
--   The Psi construction uses the run Height append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L138-L142
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L138-L142

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.runHeight_append (p q : List Bool) (h : Int) :
    runHeight (p ++ q) h = runHeight q (runHeight p h) := by sorry
