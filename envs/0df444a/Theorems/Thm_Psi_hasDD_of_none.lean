-- Prove2me | Theorems.Thm_Psi_hasDD_of_none
-- name    : Psi.hasDD_of_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:16:58.548272+00:00
-- url     : https://prove2.me/theorems/81a4b094-dafd-4a17-a5a1-04134805cca9
-- title:
--   Psi: has DD of none
-- statement:
--   `firstDDidx` returning `none` means no `DD`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L417-L441
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L417-L441

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem Psi.hasDD_of_none (l : List Bool) (hn : firstDDidx l = none) : hasDD l = false := by sorry
