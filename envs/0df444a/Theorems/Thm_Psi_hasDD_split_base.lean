-- Prove2me | Theorems.Thm_Psi_hasDD_split_base
-- name    : Psi.hasDD_split_base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:11:28.010666+00:00
-- url     : https://prove2.me/theorems/2ac9553d-6f16-4283-8a92-b0c2ab7ea954
-- title:
--   Psi: has DD split base
-- statement:
--   Base-case structural bound: any split of the base path `((UD)^l U^{k+1} D^{k+1})`
--   at a row `h ≤ l + k + 1` has no `DD` in its first piece.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L258-L282
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L258-L282

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.hasDD_split_base (l k h : ℕ) (hh : h ≤ l + k + 1) :
    hasDD (splitAtRow ((List.replicate l [true, false]).flatten ++ List.replicate (k + 1) true
      ++ List.replicate (k + 1) false) h).1 = false := by sorry
