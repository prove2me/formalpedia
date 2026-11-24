-- Prove2me | Theorems.Thm_Psi_phi_size
-- name    : Psi.phi_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:02:17.116946+00:00
-- url     : https://prove2.me/theorems/e8a7e8a7-5a58-45bc-b4a9-b628b4740603
-- title:
--   Psi: phi size
-- statement:
--   `Φ` produces a path of the expected size `2n`, `n = |w| + 1` (no validity of
--   the area vector is needed).
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PhiBasic.lean#L36-L58
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PhiBasic.lean#L36-L58

import Definitions.Def_RequestProject_Psi_PathLemmas
import Definitions.Def_RequestProject_Psi_PhiBasic
set_option autoImplicit true
open Psi

theorem Psi.phi_size (w : List Bool) (av : List ℕ) :
    (phiPath w av).length = 2 * (w.length + 1) := by sorry
