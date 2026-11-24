-- Prove2me | Theorems.Thm_Psi_noDD_numE
-- name    : Psi.noDD_numE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:11:32.670312+00:00
-- url     : https://prove2.me/theorems/1385315d-15c6-4069-877c-d6f3a6c9abdc
-- title:
--   Psi: no DD num E
-- statement:
--   For a path with no `DD`, the number of East steps equals the number of
--   valleys plus one if the path ends in an East step (each maximal East-run has
--   length one, and each is followed by a North except possibly a final one).
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L287-L320
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L287-L320

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.noDD_numE (p : List Bool) (hp : hasDD p = false) :
    numE p = numValleys p + (if stEast p false then 1 else 0) := by sorry
