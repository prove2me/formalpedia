-- Prove2me | Theorems.Thm_Psi_fUD_len
-- name    : Psi.fUD_len
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:00:22.449143+00:00
-- url     : https://prove2.me/theorems/1fca3925-e1b0-4139-a684-7c57d3c32b2a
-- title:
--   Psi: f UD len
-- statement:
--   The Psi construction uses the f UD len property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L273-L276
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L273-L276

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem Psi.fUD_len (n : ℕ) : (List.replicate n [true, false]).flatten.length = 2 * n := by sorry
