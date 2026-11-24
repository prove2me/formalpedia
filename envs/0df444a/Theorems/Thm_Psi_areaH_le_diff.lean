-- Prove2me | Theorems.Thm_Psi_areaH_le_diff
-- name    : Psi.areaH_le_diff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:11:40.002579+00:00
-- url     : https://prove2.me/theorems/e2f415a1-cd08-4158-9ba0-49286b8ef230
-- title:
--   Psi: area H le diff
-- statement:
--   Effect of the incoming `le` flag on `areaH`: turning it on adds the current
--   height exactly when the path starts with a North step.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L324-L328
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L324-L328

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.areaH_le_diff (q : List Bool) (ht : Int) :
    areaH q ht true - areaH q ht false = (if q.head? = some true then ht else 0) := by sorry
