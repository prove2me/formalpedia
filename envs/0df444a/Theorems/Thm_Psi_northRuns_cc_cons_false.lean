-- Prove2me | Theorems.Thm_Psi_northRuns_cc_cons_false
-- name    : Psi.northRuns_cc_cons_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:03:20.055941+00:00
-- url     : https://prove2.me/theorems/1cbe2a63-4fc3-4b2d-98a7-ecff6a82b58e
-- title:
--   Psi: north Runs cc cons false
-- statement:
--   The Psi construction uses the north Runs cc cons false property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L214-L223
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L214-L223

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp
set_option autoImplicit true
open Psi

theorem Psi.northRuns_cc_cons_false (X : List Bool) :
    northRuns (cc (false :: X)) = northRuns (cc X) := by sorry
