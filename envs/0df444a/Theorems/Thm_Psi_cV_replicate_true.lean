-- Prove2me | Theorems.Thm_Psi_cV_replicate_true
-- name    : Psi.cV_replicate_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:01:40.486171+00:00
-- url     : https://prove2.me/theorems/55769d8b-1676-4068-ade2-277601c84741
-- title:
--   Psi: c V replicate true
-- statement:
--   The Psi construction uses the c V replicate true property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L281-L291
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L281-L291

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.cV_replicate_true (n : Nat) (le : Bool) :
    countValleys (List.replicate n true) le = (if le ∧ 1 ≤ n then 1 else 0) := by sorry
