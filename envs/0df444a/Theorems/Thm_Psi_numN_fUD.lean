-- Prove2me | Theorems.Thm_Psi_numN_fUD
-- name    : Psi.numN_fUD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:53:23.149805+00:00
-- url     : https://prove2.me/theorems/aa4aea3a-2061-4ae1-95d1-1dcf15a774ad
-- title:
--   Psi: num N f UD
-- statement:
--   The Psi construction uses the num N f UD property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PhiBasic.lean#L108-L112
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PhiBasic.lean#L108-L112

import Definitions.Def_RequestProject_Psi_PathLemmas
import Definitions.Def_RequestProject_Psi_PhiBasic
set_option autoImplicit true
open Psi

theorem Psi.numN_fUD (a : Nat) : numN (fUD a) = a := by sorry
