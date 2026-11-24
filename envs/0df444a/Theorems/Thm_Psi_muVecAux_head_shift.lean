-- Prove2me | Theorems.Thm_Psi_muVecAux_head_shift
-- name    : Psi.muVecAux_head_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:12:26.564383+00:00
-- url     : https://prove2.me/theorems/10409afc-5771-4c8f-8900-a294afb30288
-- title:
--   Psi: mu Vec Aux head shift
-- statement:
--   The Psi construction uses the mu Vec Aux head shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L39-L48
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L39-L48

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp
set_option autoImplicit true
open Psi

theorem Psi.muVecAux_head_shift (L : List ℕ) (hpt : ℕ) (hL : 0 < L.headD 0) :
    muVecAux L hpt = ppart (L.headD 0 - hpt) ++ (muVec L).tail := by sorry
