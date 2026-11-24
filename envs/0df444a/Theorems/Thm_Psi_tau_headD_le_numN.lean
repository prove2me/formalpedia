-- Prove2me | Theorems.Thm_Psi_tau_headD_le_numN
-- name    : Psi.tau_headD_le_numN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:56:40.405589+00:00
-- url     : https://prove2.me/theorems/44383fde-e6fc-4808-9b25-f3ed427b277a
-- title:
--   Psi: tau head D le num N
-- statement:
--   The head of `tauOf` is at most its last entry (a `≤`-chain), hence
--   `≤ #North(phiPath w' av') = |w'| + 1`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L650-L654
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L650-L654

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.tau_headD_le_numN (w' : List Bool) (av' : List ℕ) (hv : IsValid w' av') :
    (tauOf w' av').headD 0 ≤ numN (phiPath w' av') := by sorry
