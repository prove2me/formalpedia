-- Prove2me | Theorems.Thm_Psi_runHeight_shift
-- name    : Psi.runHeight_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:57:16.851016+00:00
-- url     : https://prove2.me/theorems/beaa1ffb-537d-4662-a28e-9c3c385642ab
-- title:
--   Psi: run Height shift
-- statement:
--   The Psi construction uses the run Height shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L182-L188
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L182-L188

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.runHeight_shift (p : List Bool) (h d : Int) :
    runHeight p (h + d) = runHeight p h + d := by sorry
