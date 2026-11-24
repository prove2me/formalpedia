-- Prove2me | Theorems.Thm_Psi_noDD_high
-- name    : Psi.noDD_high
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:16:40.147038+00:00
-- url     : https://prove2.me/theorems/d315ce67-0d73-40bc-b07a-8d4b10b10486
-- title:
--   Psi: no DD high
-- statement:
--   A path from height `≥ 2` cannot return to `0` without a `DD` (no two
--   consecutive East steps).
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L375-L414
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L375-L414

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem Psi.noDD_high : ∀ (k : ℕ) (r : List Bool) (h : ℤ), r.length = k → 2 ≤ h →
    validFrom r h → runHeight r h = 0 → hasDD r = false → False := by sorry
