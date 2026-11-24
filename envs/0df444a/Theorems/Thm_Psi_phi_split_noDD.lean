-- Prove2me | Theorems.Thm_Psi_phi_split_noDD
-- name    : Psi.phi_split_noDD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:58:20.844179+00:00
-- url     : https://prove2.me/theorems/f99c121c-8111-4c2d-b99a-59216732a9a2
-- title:
--   Psi: phi split no DD
-- statement:
--   Structural key lemma (`STRUCT`): splitting `phiPath w' av'` at a row `h`
--   bounded by the first coordinate of `τ' = tauOf w' av'` never exposes a `DD`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L658-L714
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L658-L714

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.phi_split_noDD (w' : List Bool) (av' : List ℕ) (hv : IsValid w' av')
    (h : ℕ) (hle : h ≤ (tauOf w' av').headD 0) :
    hasDD (splitAtRow (phiPath w' av') h).1 = false := by sorry
