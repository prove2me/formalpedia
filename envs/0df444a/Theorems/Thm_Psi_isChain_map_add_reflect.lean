-- Prove2me | Theorems.Thm_Psi_isChain_map_add_reflect
-- name    : Psi.isChain_map_add_reflect
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:12:15.22067+00:00
-- url     : https://prove2.me/theorems/023cc3f9-2143-44f1-bcf4-3649f48e6038
-- title:
--   Psi: is Chain map add reflect
-- statement:
--   The Psi construction uses the is Chain map add reflect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L519-L528
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L519-L528

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.isChain_map_add_reflect (l : List ℕ) (c : ℕ)
    (h : (l.map (· + c)).IsChain (· ≤ ·)) : l.IsChain (· ≤ ·) := by sorry
