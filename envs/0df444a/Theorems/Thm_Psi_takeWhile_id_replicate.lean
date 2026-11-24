-- Prove2me | Theorems.Thm_Psi_takeWhile_id_replicate
-- name    : Psi.takeWhile_id_replicate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:15:46.885273+00:00
-- url     : https://prove2.me/theorems/86350a3f-e258-4103-98d7-94b3d578f359
-- title:
--   Psi: take While id replicate
-- statement:
--   `takeWhile id` of a `Bool` list is an all-North run.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L8-L15
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L8-L15

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem Psi.takeWhile_id_replicate (xs : List Bool) :
    xs.takeWhile id = List.replicate (xs.takeWhile id).length true := by sorry
