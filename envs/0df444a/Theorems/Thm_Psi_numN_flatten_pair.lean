-- Prove2me | Theorems.Thm_Psi_numN_flatten_pair
-- name    : Psi.numN_flatten_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:10:18.247312+00:00
-- url     : https://prove2.me/theorems/a6b8c164-f8cb-4910-8a63-02f6159da2cb
-- title:
--   Psi: num N flatten pair
-- statement:
--   The Psi construction uses the num N flatten pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PhiBasic.lean#L141-L142
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PhiBasic.lean#L141-L142

import Definitions.Def_RequestProject_Psi_PathLemmas
import Definitions.Def_RequestProject_Psi_PhiBasic
set_option autoImplicit true
open Psi

theorem Psi.numN_flatten_pair (l : Nat) :
    numN ((List.replicate l [true, false]).flatten) = l := by sorry
