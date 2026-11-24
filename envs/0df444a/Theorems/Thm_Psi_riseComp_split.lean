-- Prove2me | Theorems.Thm_Psi_riseComp_split
-- name    : Psi.riseComp_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:13:24.827818+00:00
-- url     : https://prove2.me/theorems/31944504-1076-4ca2-89ab-5113457aa29e
-- title:
--   Psi: rise Comp split
-- statement:
--   Key geometric identity: the rise composition of `cc ρ'` is obtained from that
--   of `cc (ρ ++ ρ')` by cutting `numN ρ` off the first run.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L268-L282
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L268-L282

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp
set_option autoImplicit true
open Psi

theorem Psi.riseComp_split (rho rho' : List Bool) (hrho : hasDD rho = false) :
    northRuns (cc rho')
      = ppart ((northRuns (cc (rho ++ rho'))).headD 0 - numN rho)
        ++ (northRuns (cc (rho ++ rho'))).tail := by sorry
