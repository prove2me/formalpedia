-- Prove2me | Theorems.Thm_Psi_split_numN
-- name    : Psi.split_numN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:55:49.591605+00:00
-- url     : https://prove2.me/theorems/646fe7ff-04b9-48ad-b65c-d670ee77373b
-- title:
--   Psi: split num N
-- statement:
--   `splitAtRow` at row `h` yields a first piece with exactly `h` North steps
--   (provided `h` does not exceed the total number of North steps).
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L121-L133
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L121-L133

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.split_numN (pi : List Bool) (h : ℕ) (hh : h ≤ numN pi) :
    numN (splitAtRow pi h).1 = h := by sorry
