-- Prove2me | Theorems.Thm_Psi_hasDD_cons
-- name    : Psi.hasDD_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:52:07.077028+00:00
-- url     : https://prove2.me/theorems/94e2ac70-e79d-4e9e-bafa-ae3272f1dccc
-- title:
--   Psi: has DD cons
-- statement:
--   The Psi construction uses the has DD cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L141-L147
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L141-L147

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.hasDD_cons (a : Bool) (rest : List Bool) :
    hasDD (a :: rest) = ((a == false && rest.head? == some false) || hasDD rest) := by sorry
