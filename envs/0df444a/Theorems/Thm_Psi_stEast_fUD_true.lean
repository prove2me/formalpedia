-- Prove2me | Theorems.Thm_Psi_stEast_fUD_true
-- name    : Psi.stEast_fUD_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:09:16.089431+00:00
-- url     : https://prove2.me/theorems/6084c9be-4484-460a-b830-21e42f768850
-- title:
--   Psi: st East f UD true
-- statement:
--   The Psi construction uses the st East f UD true property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L317-L320
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L317-L320

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.stEast_fUD_true (a : Nat) : stEast (fUD a) true = true := by sorry
