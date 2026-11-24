-- Prove2me | Theorems.Thm_Psi_noDescent_true_eq
-- name    : Psi.noDescent_true_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:15:06.208574+00:00
-- url     : https://prove2.me/theorems/b8baad00-4425-4c0d-9617-80738ffea311
-- title:
--   Psi: no Descent true eq
-- statement:
--   A word with no descent is `0^l 1^k`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L357-L393
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L357-L393

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward
set_option autoImplicit true
open Psi

theorem Psi.noDescent_true_eq (w : List Bool) (h : noDescent w = true) :
    w = List.replicate (w.filter (· = false)).length false
          ++ List.replicate (w.filter id).length true := by sorry
