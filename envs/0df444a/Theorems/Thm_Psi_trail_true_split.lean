-- Prove2me | Theorems.Thm_Psi_trail_true_split
-- name    : Psi.trail_true_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:15:57.680941+00:00
-- url     : https://prove2.me/theorems/92554da8-b3c9-4a49-8c77-8112f5d8c1b2
-- title:
--   Psi: trail true split
-- statement:
--   Trailing North-run split (with the pre-run part not ending in a North step).
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L57-L74
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L57-L74

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem Psi.trail_true_split (A : List Bool) :
    A = A.take (A.length - (A.reverse.takeWhile id).length)
          ++ List.replicate ((A.reverse.takeWhile id).length) true
      ∧ (A.take (A.length - (A.reverse.takeWhile id).length)).getLast? ≠ some true := by sorry
