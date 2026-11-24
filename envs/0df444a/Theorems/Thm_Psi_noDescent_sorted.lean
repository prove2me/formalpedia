-- Prove2me | Theorems.Thm_Psi_noDescent_sorted
-- name    : Psi.noDescent_sorted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:50:39.920898+00:00
-- url     : https://prove2.me/theorems/1833db47-8197-4fe6-938d-e0c4577e65d9
-- title:
--   Psi: no Descent sorted
-- statement:
--   The Psi construction uses the no Descent sorted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L70-L74
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L70-L74

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.noDescent_sorted (a b : ℕ) :
    noDescent (List.replicate a false ++ List.replicate b true) = true := by sorry
