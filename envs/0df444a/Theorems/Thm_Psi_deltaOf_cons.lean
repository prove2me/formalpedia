-- Prove2me | Theorems.Thm_Psi_deltaOf_cons
-- name    : Psi.deltaOf_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:02:47.181513+00:00
-- url     : https://prove2.me/theorems/a1c6f56b-5074-499e-89df-86325f0978d5
-- title:
--   Psi: delta Of cons
-- statement:
--   The Psi construction uses the delta Of cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L406-L408
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L406-L408

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.deltaOf_cons (x : ℕ) (r : List ℕ) :
    deltaOf (x :: r) = x :: (deltaOf r).map (· + x) := by sorry
