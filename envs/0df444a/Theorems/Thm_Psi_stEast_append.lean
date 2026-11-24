-- Prove2me | Theorems.Thm_Psi_stEast_append
-- name    : Psi.stEast_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:53:43.402435+00:00
-- url     : https://prove2.me/theorems/8c0680b9-66d1-4775-8c3d-89bc028f47e6
-- title:
--   Psi: st East append
-- statement:
--   The Psi construction uses the st East append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L276-L280
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L276-L280

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.stEast_append (p q : List Bool) (x : Bool) :
    stEast (p ++ q) x = stEast q (stEast p x) := by sorry
