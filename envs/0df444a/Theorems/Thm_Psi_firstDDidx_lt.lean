-- Prove2me | Theorems.Thm_Psi_firstDDidx_lt
-- name    : Psi.firstDDidx_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:16:16.361167+00:00
-- url     : https://prove2.me/theorems/f4cf3e55-d712-46a4-958d-a3a0a5cae60d
-- title:
--   Psi: first DDidx lt
-- statement:
--   The `DD` lies within the path bounds.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L94-L104
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L94-L104

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem Psi.firstDDidx_lt (rest : List Bool) (i : ℕ) (h : firstDDidx rest = some i) :
    i + 1 < rest.length := by sorry
