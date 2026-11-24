-- Prove2me | Theorems.Thm_Psi_takeWhile_false_replicate
-- name    : Psi.takeWhile_false_replicate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:15:43.841821+00:00
-- url     : https://prove2.me/theorems/1fd885da-ca9f-4e25-8c6d-0fa52d148d94
-- title:
--   Psi: take While false replicate
-- statement:
--   `takeWhile (· = false)` of a `Bool` list is an all-East run.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L18-L25
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L18-L25

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem Psi.takeWhile_false_replicate (xs : List Bool) :
    xs.takeWhile (· = false) = List.replicate (xs.takeWhile (· = false)).length false := by sorry
