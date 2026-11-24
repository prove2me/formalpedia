-- Prove2me | Theorems.Thm_Psi_isChain_head_le_getLast
-- name    : Psi.isChain_head_le_getLast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:12:09.217824+00:00
-- url     : https://prove2.me/theorems/e731e649-be4b-4b86-8abd-bc4c1c8ba72e
-- title:
--   Psi: is Chain head le get Last
-- statement:
--   The Psi construction uses the is Chain head le get Last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L505-L517
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L505-L517

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.isChain_head_le_getLast (l : List ℕ) (hc : l.IsChain (· ≤ ·)) (g : ℕ)
    (hg : l.getLast? = some g) : l.headD 0 ≤ g := by sorry
