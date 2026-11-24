-- Prove2me | Theorems.Thm_Psi_takeWhile_repl_false
-- name    : Psi.takeWhile_repl_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:14:31.234359+00:00
-- url     : https://prove2.me/theorems/6231d144-6c41-456e-bdf6-e3bbd5958ef4
-- title:
--   Psi: take While repl false
-- statement:
--   `takeWhile (· = false)` passes through a leading `E^m`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L192-L197
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L192-L197

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward
set_option autoImplicit true
open Psi

theorem Psi.takeWhile_repl_false (m : ℕ) (X : List Bool) :
    (List.replicate m false ++ X).takeWhile (· = false)
      = List.replicate m false ++ X.takeWhile (· = false) := by sorry
