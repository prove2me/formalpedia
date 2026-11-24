-- Prove2me | Theorems.Thm_Psi_riseComp_recon
-- name    : Psi.riseComp_recon
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:13:38.230816+00:00
-- url     : https://prove2.me/theorems/6b8fd1f9-bbb6-4c1d-a4e6-5bc9534c3c42
-- title:
--   Psi: rise Comp recon
-- statement:
--   Geometry of the reconstructed path: contracting and taking rise runs yields a
--   first run of length `a+1+b+h` followed by the runs of `cc ρ'`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L297-L322
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L297-L322

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp
set_option autoImplicit true
open Psi

theorem Psi.riseComp_recon (a b hh : ℕ) (rho rho' : List Bool) (hb : 1 ≤ b)
    (hnoDD : hasDD rho = false) (hnumN : numN rho = hh) :
    northRuns (cc ((List.replicate a [true, false]).flatten ++ [true] ++ rho
        ++ List.replicate b true ++ List.replicate (b + 1) false ++ rho'))
      = (a + 1 + b + hh) :: northRuns (cc rho') := by sorry
