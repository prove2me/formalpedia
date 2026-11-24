-- Prove2me | Theorems.Thm_Psi_cLead0_block
-- name    : Psi.cLead0_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:00:06.149277+00:00
-- url     : https://prove2.me/theorems/b1a3e5aa-e1d3-471c-9aa3-c3351b15579c
-- title:
--   Psi: c Lead0 block
-- statement:
--   The Psi construction uses the c Lead0 block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L581-L586
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L581-L586

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem Psi.cLead0_block (a b : ℕ) (w' : List Bool) (hb : 1 ≤ b) :
    cLead0 (List.replicate a false ++ List.replicate b true ++ false :: w') = a := by sorry
