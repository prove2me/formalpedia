-- Prove2me | Theorems.Thm_Psi_northRuns_replicate_true_replicate_false
-- name    : Psi.northRuns_replicate_true_replicate_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:13:09.555556+00:00
-- url     : https://prove2.me/theorems/885c2b48-8283-4b30-80ec-8835563b4e2b
-- title:
--   Psi: north Runs replicate true replicate false
-- statement:
--   The Psi construction uses the north Runs replicate true replicate false property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L232-L247
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L232-L247

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp
set_option autoImplicit true
open Psi

theorem Psi.northRuns_replicate_true_replicate_false (m n : ℕ) (hm : 0 < m) :
    northRuns (List.replicate m true ++ List.replicate n false) = [m] := by sorry
