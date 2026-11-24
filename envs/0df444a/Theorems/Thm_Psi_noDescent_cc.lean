-- Prove2me | Theorems.Thm_Psi_noDescent_cc
-- name    : Psi.noDescent_cc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:17:25.863855+00:00
-- url     : https://prove2.me/theorems/9b590ed7-8ce6-4a39-8252-6b420e0a9943
-- title:
--   Psi: no Descent cc
-- statement:
--   The Psi construction uses the no Descent cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L558-L559
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L558-L559

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem Psi.noDescent_cc (x y : Bool) (r : List Bool) :
    noDescent (x :: y :: r) = ((!x || y) && noDescent (y :: r)) := by sorry
