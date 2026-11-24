-- Prove2me | Theorems.Thm_Psi_dropWhile_eq_drop
-- name    : Psi.dropWhile_eq_drop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:16:06.336946+00:00
-- url     : https://prove2.me/theorems/f9d91e5f-524e-4db7-a927-434ad29d7645
-- title:
--   Psi: drop While eq drop
-- statement:
--   `dropWhile` is a `drop` by the `takeWhile` length.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L28-L33
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L28-L33

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem Psi.dropWhile_eq_drop {α} (p : α → Bool) (l : List α) :
    l.dropWhile p = l.drop (l.takeWhile p).length := by sorry
