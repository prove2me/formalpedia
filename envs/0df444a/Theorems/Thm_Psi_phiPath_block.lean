-- Prove2me | Theorems.Thm_Psi_phiPath_block
-- name    : Psi.phiPath_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:17:27.196434+00:00
-- url     : https://prove2.me/theorems/fd3f8ee5-c0c7-4b1f-a99b-8962d8c1485b
-- title:
--   Psi: phi Path block
-- statement:
--   `Φ` on the recursive word `0^a 1^b 0 w'` performs the split reconstruction.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L606-L615
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L606-L615

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem Psi.phiPath_block (a b : ℕ) (w' : List Bool) (h : ℕ) (av' : List ℕ) (hb : 1 ≤ b) :
    phiPath (List.replicate a false ++ List.replicate b true ++ [false] ++ w') (h :: av')
      = (List.replicate a [true, false]).flatten ++ [true]
          ++ (splitAtRow (phiPath w' av') h).1 ++ List.replicate b true
          ++ List.replicate (b + 1) false ++ (splitAtRow (phiPath w' av') h).2 := by sorry
