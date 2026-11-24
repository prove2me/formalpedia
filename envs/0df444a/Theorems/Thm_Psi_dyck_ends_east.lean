-- Prove2me | Theorems.Thm_Psi_dyck_ends_east
-- name    : Psi.dyck_ends_east
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:09:37.835795+00:00
-- url     : https://prove2.me/theorems/76fa89f3-bf66-4e77-b8c0-42fbed228d6d
-- title:
--   Psi: dyck ends east
-- statement:
--   The Psi construction uses the dyck ends east property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L357-L369
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L357-L369

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.dyck_ends_east (p : List Bool) (hd : IsDyck p) (hne : p ≠ []) :
    p.getLast? = some false := by sorry
