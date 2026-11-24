-- Prove2me | Theorems.Thm_Psi_stEast_replicate_true
-- name    : Psi.stEast_replicate_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:55:05.225947+00:00
-- url     : https://prove2.me/theorems/9d750c71-ed8e-4bf5-a1d2-7e541703bd49
-- title:
--   Psi: st East replicate true
-- statement:
--   The Psi construction uses the st East replicate true property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L297-L301
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L297-L301

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.stEast_replicate_true (n : Nat) (x : Bool) :
    stEast (List.replicate n true) x = if 1 ≤ n then false else x := by sorry
