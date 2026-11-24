-- Prove2me | Theorems.Thm_Psi_tauOf_head_pos
-- name    : Psi.tauOf_head_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:12:35.028136+00:00
-- url     : https://prove2.me/theorems/d2e72ee4-6683-4fee-8ecd-e98a50dc3232
-- title:
--   Psi: tau Of head pos
-- statement:
--   The Psi construction uses the tau Of head pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L67-L79
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L67-L79

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp
set_option autoImplicit true
open Psi

theorem Psi.tauOf_head_pos (w : List Bool) (av : List ℕ) (hv : IsValid w av) :
    0 < (tauOf w av).headD 0 := by sorry
