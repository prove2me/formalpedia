-- Prove2me | Theorems.Thm_Psi_stEast_replicate_false
-- name    : Psi.stEast_replicate_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:01:42.675169+00:00
-- url     : https://prove2.me/theorems/09a83d15-ad92-4646-8ac1-dd9720347b53
-- title:
--   Psi: st East replicate false
-- statement:
--   The Psi construction uses the st East replicate false property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L302-L306
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L302-L306

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.stEast_replicate_false (n : Nat) (x : Bool) :
    stEast (List.replicate n false) x = if 1 ≤ n then true else x := by sorry
