-- Prove2me | Theorems.Thm_Psi_zipWith_add_map
-- name    : Psi.zipWith_add_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:12:00.561124+00:00
-- url     : https://prove2.me/theorems/69483a14-89bb-4cf7-a13f-9f73a8976676
-- title:
--   Psi: zip With add map
-- statement:
--   The Psi construction uses the zip With add map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L497-L503
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L497-L503

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.zipWith_add_map (X Y : List ℕ) (c : ℕ) :
    List.zipWith (· + ·) (X.map (· + c)) Y = (List.zipWith (· + ·) X Y).map (· + c) := by sorry
