-- Prove2me | Theorems.Thm_Psi_northRuns_cc_replicate_false
-- name    : Psi.northRuns_cc_replicate_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:13:05.282814+00:00
-- url     : https://prove2.me/theorems/5cd87836-9d9c-4c81-ba3d-3cce5ee10b03
-- title:
--   Psi: north Runs cc replicate false
-- statement:
--   The Psi construction uses the north Runs cc replicate false property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L225-L230
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L225-L230

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp
set_option autoImplicit true
open Psi

theorem Psi.northRuns_cc_replicate_false (n : ℕ) (X : List Bool) :
    northRuns (cc (List.replicate n false ++ X)) = northRuns (cc X) := by sorry
