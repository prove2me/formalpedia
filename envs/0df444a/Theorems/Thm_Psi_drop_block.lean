-- Prove2me | Theorems.Thm_Psi_drop_block
-- name    : Psi.drop_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:04:17.69905+00:00
-- url     : https://prove2.me/theorems/435ef79a-b5e6-4350-bbf6-f5e33884beca
-- title:
--   Psi: drop block
-- statement:
--   The Psi construction uses the drop block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L594-L597
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L594-L597

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem Psi.drop_block (b : ℕ) (w' : List Bool) :
    (List.replicate b true ++ false :: w').drop (b + 1) = w' := by sorry
