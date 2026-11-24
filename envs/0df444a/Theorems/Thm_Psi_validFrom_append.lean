-- Prove2me | Theorems.Thm_Psi_validFrom_append
-- name    : Psi.validFrom_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:50:46.816995+00:00
-- url     : https://prove2.me/theorems/db391565-a2ad-479b-9db8-c58d1a054243
-- title:
--   Psi: valid From append
-- statement:
--   The Psi construction uses the valid From append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L144-L148
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L144-L148

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.validFrom_append (p q : List Bool) (h : Int) :
    validFrom (p ++ q) h ↔ validFrom p h ∧ validFrom q (runHeight p h) := by sorry
