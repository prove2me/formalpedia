-- Prove2me | Theorems.Thm_Psi_head_dropWhile_id
-- name    : Psi.head_dropWhile_id
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:16:00.637631+00:00
-- url     : https://prove2.me/theorems/5f516d81-2d6e-42e0-869c-d374fc1e2dfa
-- title:
--   Psi: head drop While id
-- statement:
--   The Psi construction uses the head drop While id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L35-L38
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L35-L38

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem Psi.head_dropWhile_id (l : List Bool) : (l.dropWhile id).head? ≠ some true := by sorry
