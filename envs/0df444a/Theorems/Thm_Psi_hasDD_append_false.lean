-- Prove2me | Theorems.Thm_Psi_hasDD_append_false
-- name    : Psi.hasDD_append_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:56:18.400793+00:00
-- url     : https://prove2.me/theorems/24cf8c31-2856-41ba-815e-a26e8f699f17
-- title:
--   Psi: has DD append false
-- statement:
--   No `DD` is preserved by concatenation provided the boundary does not create
--   one (either the left part does not end in an East step, or the right part does
--   not start with one).
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L152-L182
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L152-L182

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.hasDD_append_false (s t : List Bool) (hs : hasDD s = false) (ht : hasDD t = false)
    (hbound : stEast s false = true → t.head? ≠ some false) : hasDD (s ++ t) = false := by sorry
