-- Prove2me | Theorems.Thm_Psi_firstDDidx_take_noDD
-- name    : Psi.firstDDidx_take_noDD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:16:27.707713+00:00
-- url     : https://prove2.me/theorems/8195697e-edc7-4ac5-bf77-c92ac4a6094b
-- title:
--   Psi: first DDidx take no DD
-- statement:
--   No `DD` occurs strictly before the first one.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L120-L139
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L120-L139

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem Psi.firstDDidx_take_noDD (rest : List Bool) (i : ℕ) (h : firstDDidx rest = some i) :
    hasDD (rest.take i) = false := by sorry
