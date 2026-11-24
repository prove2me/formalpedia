-- Prove2me | Theorems.Thm_Psi_firstDDidx_repl_true_DD
-- name    : Psi.firstDDidx_repl_true_DD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:03:23.943921+00:00
-- url     : https://prove2.me/theorems/acf6e6d0-701f-413c-bc89-f7b98eb47e37
-- title:
--   Psi: first DDidx repl true DD
-- statement:
--   `firstDDidx` of `U^m` followed by a `DD` is `m`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L151-L155
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L151-L155

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward
set_option autoImplicit true
open Psi

theorem Psi.firstDDidx_repl_true_DD (m : ℕ) (r : List Bool) :
    firstDDidx (List.replicate m true ++ false :: false :: r) = some m := by sorry
