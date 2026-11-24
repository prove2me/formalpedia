-- Prove2me | Theorems.Thm_Psi_noDescent_false_decomp
-- name    : Psi.noDescent_false_decomp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:50:33.656438+00:00
-- url     : https://prove2.me/theorems/5daab9ff-10f1-4247-b131-c516775e93da
-- title:
--   Psi: no Descent false decomp
-- statement:
--   When `w` has a descent, it decomposes as `0^a 1^b 0 w'` with `b ≥ 1`, where
--   `a`, `b`, `w'` are exactly the quantities used by `phiPath`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L78-L118
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L78-L118

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.noDescent_false_decomp {w : List Bool} (hw : noDescent w = false) :
    w = List.replicate (cLead0 w) false
          ++ List.replicate (cLead1 (w.drop (cLead0 w))) true
          ++ false :: (w.drop (cLead0 w)).drop (cLead1 (w.drop (cLead0 w)) + 1)
        ∧ 1 ≤ cLead1 (w.drop (cLead0 w)) := by sorry
