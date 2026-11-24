-- Prove2me | Theorems.Thm_Psi_drop_a_block
-- name    : Psi.drop_a_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:00:24.986607+00:00
-- url     : https://prove2.me/theorems/f44550da-7e04-4a3d-8af1-b1f0914254eb
-- title:
--   Psi: drop a block
-- statement:
--   The Psi construction uses the drop a block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L599-L603
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L599-L603

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem Psi.drop_a_block (a b : ℕ) (w' : List Bool) :
    (List.replicate a false ++ List.replicate b true ++ false :: w').drop a
      = List.replicate b true ++ false :: w' := by sorry
