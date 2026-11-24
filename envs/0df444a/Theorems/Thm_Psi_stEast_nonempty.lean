-- Prove2me | Theorems.Thm_Psi_stEast_nonempty
-- name    : Psi.stEast_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:55:04.36955+00:00
-- url     : https://prove2.me/theorems/318879fe-ca68-466c-9cf2-34829680f38b
-- title:
--   Psi: st East nonempty
-- statement:
--   The Psi construction uses the st East nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L337-L343
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L337-L343

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.stEast_nonempty (p : List Bool) (hp : p ≠ []) (x y : Bool) :
    stEast p x = stEast p y := by sorry
