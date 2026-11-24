-- Prove2me | Theorems.Thm_Psi_isValid_base_sum
-- name    : Psi.isValid_base_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:12:15.831484+00:00
-- url     : https://prove2.me/theorems/ad317f74-5a5c-4c90-98a3-1a37c633b848
-- title:
--   Psi: is Valid base sum
-- statement:
--   In the base case (`w` weakly increasing) validity forces `Σ av = 0`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L632-L646
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L632-L646

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.isValid_base_sum (w : List Bool) (av : List ℕ) (hv : IsValid w av)
    (hnd : noDescent w = true) : av.sum = 0 := by sorry
