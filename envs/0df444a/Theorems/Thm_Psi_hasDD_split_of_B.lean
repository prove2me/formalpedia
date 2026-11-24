-- Prove2me | Theorems.Thm_Psi_hasDD_split_of_B
-- name    : Psi.hasDD_split_of_B
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:02:42.833599+00:00
-- url     : https://prove2.me/theorems/af4a1f6c-7ff2-478f-bbc5-71827de36f3a
-- title:
--   Psi: has DD split of B
-- statement:
--   Combining lemma: if `B` has no `DD`, ends in an East step, and has at least
--   `h` North steps, then the split of `B ++ C` at row `h` has no `DD`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L250-L254
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L250-L254

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.hasDD_split_of_B (B C : List Bool) (h : ℕ) (hBend : stEast B false = true)
    (hBnum : h ≤ numN B) (hBnoDD : hasDD B = false) :
    hasDD (splitAtRow (B ++ C) h).1 = false := by sorry
