-- Prove2me | Theorems.Thm_Psi_phi_numValleys
-- name    : Psi.phi_numValleys
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:10:03.833064+00:00
-- url     : https://prove2.me/theorems/afac9bc0-f130-49c8-93e1-16a28f381f33
-- title:
--   Psi: phi num Valleys
-- statement:
--   The produced path has exactly `#0(w)` valleys: `w ∈ W(0^l, 1^k)` with `l` the
--   number of valleys.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PhiBasic.lean#L62-L94
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PhiBasic.lean#L62-L94

import Definitions.Def_RequestProject_Psi_PathLemmas
import Definitions.Def_RequestProject_Psi_PhiBasic
set_option autoImplicit true
open Psi

theorem Psi.phi_numValleys (w : List Bool) (av : List ℕ) :
    numValleys (phiPath w av) = (w.filter (· = false)).length := by sorry
