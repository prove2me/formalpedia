-- Prove2me | Theorems.Thm_Psi_cVstate_fUD
-- name    : Psi.cVstate_fUD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:01:51.326842+00:00
-- url     : https://prove2.me/theorems/033d8d81-e5b3-4843-b3db-ee08480fd8e6
-- title:
--   Psi: c Vstate f UD
-- statement:
--   The Psi construction uses the c Vstate f UD property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L323-L329
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L323-L329

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.cVstate_fUD (a : Nat) :
    countValleys (fUD a) false + (if stEast (fUD a) false then 1 else 0) = a := by sorry
