-- Prove2me | Theorems.Thm_Psi_cc_replicate_false
-- name    : Psi.cc_replicate_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:12:57.686044+00:00
-- url     : https://prove2.me/theorems/71f87139-d3a1-47ac-b435-8d57d8167b92
-- title:
--   Psi: cc replicate false
-- statement:
--   The Psi construction uses the cc replicate false property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L155-L163
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/RiseComp.lean#L155-L163

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp
set_option autoImplicit true
open Psi

theorem Psi.cc_replicate_false (n : ℕ) : cc (List.replicate n false) = List.replicate n false := by sorry
