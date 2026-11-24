-- Prove2me | Theorems.Thm_Psi_tauOf_descent
-- name    : Psi.tauOf_descent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:53:45.766708+00:00
-- url     : https://prove2.me/theorems/860616cb-2e4c-4315-8efb-b1ae60ec652d
-- title:
--   Psi: tau Of descent
-- statement:
--   Structure of `tauOf` under the descent recursion `w = 0^a 1^b 0 w'`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L552-L560
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L552-L560

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.tauOf_descent {w : List Bool} (hnd : noDescent w = false) (ha : ℕ) (av' : List ℕ) :
    tauOf w (ha :: av') =
      ((cLead0 w + 1 + cLead1 (w.drop (cLead0 w))) + ha)
        :: (tauOf ((w.drop (cLead0 w)).drop (cLead1 (w.drop (cLead0 w)) + 1)) av').map
            (· + (cLead0 w + 1 + cLead1 (w.drop (cLead0 w)))) := by sorry
