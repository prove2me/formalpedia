-- Prove2me | Theorems.Thm_Psi_stEast_fUD_false_pos
-- name    : Psi.stEast_fUD_false_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:09:19.771746+00:00
-- url     : https://prove2.me/theorems/b37d9a22-3dc8-4268-99c8-a0e793c827fc
-- title:
--   Psi: st East f UD false pos
-- statement:
--   The Psi construction uses the st East f UD false pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L321-L322
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L321-L322

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.stEast_fUD_false_pos (a : Nat) : stEast (fUD (a+1)) false = true := by sorry
