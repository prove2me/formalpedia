-- Prove2me | Theorems.Thm_Psi_stEast_UDpair
-- name    : Psi.stEast_UDpair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:55:14.067078+00:00
-- url     : https://prove2.me/theorems/13df34c2-d576-444d-b2e2-3e3578d24027
-- title:
--   Psi: st East UDpair
-- statement:
--   The Psi construction uses the st East UDpair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L308-L308
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L308-L308

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.stEast_UDpair (x : Bool) : stEast [true, false] x = true := by sorry
