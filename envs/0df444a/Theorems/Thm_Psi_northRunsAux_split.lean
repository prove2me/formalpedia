-- Prove2me | Theorems.Thm_Psi_northRunsAux_split
-- name    : Psi.northRunsAux_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:12:42.03181+00:00
-- url     : https://prove2.me/theorems/c655fe66-fe91-4be8-95e8-61e1f9f668d7
-- title:
--   Psi: north Runs Aux split
-- statement:
--   The Psi construction uses the north Runs Aux split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L93-L100
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L93-L100

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp
set_option autoImplicit true
open Psi

theorem Psi.northRunsAux_split (J : List Bool) (c : ℕ) :
    northRunsAux J c = ppart (c + leadN J) ++ northRuns (afterLeadRun J) := by sorry
