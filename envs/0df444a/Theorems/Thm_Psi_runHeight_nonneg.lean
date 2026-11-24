-- Prove2me | Theorems.Thm_Psi_runHeight_nonneg
-- name    : Psi.runHeight_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:01:08.942342+00:00
-- url     : https://prove2.me/theorems/dd6933d1-7a7f-4eb6-975a-53df5ff17866
-- title:
--   Psi: run Height nonneg
-- statement:
--   The Psi construction uses the run Height nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L198-L204
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L198-L204

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.runHeight_nonneg (p : List Bool) (h : Int) (hh : 0 ≤ h)
    (hv : validFrom p h) : 0 ≤ runHeight p h := by sorry
