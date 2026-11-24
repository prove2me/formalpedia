-- Prove2me | Theorems.Thm_Psi_areaH_append
-- name    : Psi.areaH_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:57:52.007252+00:00
-- url     : https://prove2.me/theorems/71ea36e1-5b27-456c-b660-aece193a0cc5
-- title:
--   Psi: area H append
-- statement:
--   The Psi construction uses the area H append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L43-L47
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L43-L47

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.areaH_append (p q : List Bool) (ht : Int) (le : Bool) :
    areaH (p ++ q) ht le = areaH p ht le + areaH q (runHeight p ht) (stEast p le) := by sorry
