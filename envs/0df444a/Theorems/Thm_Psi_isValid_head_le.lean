-- Prove2me | Theorems.Thm_Psi_isValid_head_le
-- name    : Psi.isValid_head_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:56:48.864937+00:00
-- url     : https://prove2.me/theorems/49357d38-9384-4c40-8508-91d55c6e4a44
-- title:
--   Psi: is Valid head le
-- statement:
--   Validity bounds the split row: `h = av.head ≤ (tauOf w' av').head`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L598-L621
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L598-L621

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.isValid_head_le (w : List Bool) (av : List ℕ) (hv : IsValid w av)
    (hnd : noDescent w = false) :
    av.headD 0 ≤ (tauOf ((w.drop (cLead0 w)).drop (cLead1 (w.drop (cLead0 w)) + 1)) av.tail).headD 0 := by sorry
