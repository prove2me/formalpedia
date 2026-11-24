-- Prove2me | Theorems.Thm_Psi_takeWhile_repl_true
-- name    : Psi.takeWhile_repl_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:14:27.097971+00:00
-- url     : https://prove2.me/theorems/37e8d060-0b1d-46b9-8e79-45acdaef380b
-- title:
--   Psi: take While repl true
-- statement:
--   `takeWhile id` passes through a leading `U^m`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L185-L189
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L185-L189

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward
set_option autoImplicit true
open Psi

theorem Psi.takeWhile_repl_true (m : ℕ) (X : List Bool) :
    (List.replicate m true ++ X).takeWhile id = List.replicate m true ++ X.takeWhile id := by sorry
