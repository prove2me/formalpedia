-- Prove2me | Theorems.Thm_Psi_muVec_headD
-- name    : Psi.muVec_headD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:13:27.102795+00:00
-- url     : https://prove2.me/theorems/1e296aa6-1755-4d7e-a8f2-3772dfb160e5
-- title:
--   Psi: mu Vec head D
-- statement:
--   The head of `muVec L` is the head of `L` (when positive).
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L285-L293
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L285-L293

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp
set_option autoImplicit true
open Psi

theorem Psi.muVec_headD (L : List ℕ) (hL : 0 < L.headD 0) :
    (muVec L).headD 0 = L.headD 0 := by sorry
