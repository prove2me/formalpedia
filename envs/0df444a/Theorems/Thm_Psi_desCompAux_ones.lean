-- Prove2me | Theorems.Thm_Psi_desCompAux_ones
-- name    : Psi.desCompAux_ones
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:11:46.68527+00:00
-- url     : https://prove2.me/theorems/19c3fe1a-af33-4e9f-8366-558b06e35067
-- title:
--   Psi: des Comp Aux ones
-- statement:
--   The Psi construction uses the des Comp Aux ones property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L441-L458
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L441-L458

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.desCompAux_ones (b : ℕ) (hb : 1 ≤ b) (rest : List Bool) (cur : ℕ) :
    desCompAux (List.replicate b true ++ (false :: rest)) cur
      = (cur + b) :: desCompAux (false :: rest) 0 := by sorry
