-- Prove2me | Theorems.Thm_Psi_northRunsAux_pos
-- name    : Psi.northRunsAux_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:12:56.223332+00:00
-- url     : https://prove2.me/theorems/25069ae3-ccd2-4ac8-92d0-5691ab372f03
-- title:
--   Psi: north Runs Aux pos
-- statement:
--   The Psi construction uses the north Runs Aux pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L111-L122
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L111-L122

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp
set_option autoImplicit true
open Psi

theorem Psi.northRunsAux_pos (Y : List Bool) (c : ℕ) : ∀ x ∈ northRunsAux Y c, 0 < x := by sorry
