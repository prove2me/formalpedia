-- Prove2me | Theorems.Thm_Psi_phi_numRises
-- name    : Psi.phi_numRises
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:30:08.692415+00:00
-- url     : https://prove2.me/theorems/9d2836e6-186d-4355-a65c-e18610056ac9
-- title:
--   Psi: phi num Rises
-- statement:
--   The Psi construction uses the phi num Rises property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PhiBasic.lean#L163-L173
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PhiBasic.lean#L163-L173

import Definitions.Def_RequestProject_Psi_PathLemmas
import Definitions.Def_RequestProject_Psi_PhiBasic
set_option autoImplicit true
open Psi

theorem Psi.phi_numRises (w : List Bool) (av : List ℕ) :
    numRises (phiPath w av) = (w.filter id).length := by sorry
