-- Prove2me | Theorems.Thm_Psi_numN_append
-- name    : Psi.numN_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:54:42.293042+00:00
-- url     : https://prove2.me/theorems/3d7d9e49-6b3f-4088-91ac-c20b0354d8df
-- title:
--   Psi: num N append
-- statement:
--   The Psi construction uses the num N append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PhiBasic.lean#L98-L99
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PhiBasic.lean#L98-L99

import Definitions.Def_RequestProject_Psi_PathLemmas
import Definitions.Def_RequestProject_Psi_PhiBasic
set_option autoImplicit true
open Psi

theorem Psi.numN_append (p q : List Bool) : numN (p ++ q) = numN p + numN q := by sorry
