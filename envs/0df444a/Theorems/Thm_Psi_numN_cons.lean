-- Prove2me | Theorems.Thm_Psi_numN_cons
-- name    : Psi.numN_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:10:03.902155+00:00
-- url     : https://prove2.me/theorems/ae49ed91-a698-4afc-9c48-b1b5699cac6e
-- title:
--   Psi: num N cons
-- statement:
--   The Psi construction uses the num N cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PhiBasic.lean#L114-L118
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PhiBasic.lean#L114-L118

import Definitions.Def_RequestProject_Psi_PathLemmas
import Definitions.Def_RequestProject_Psi_PhiBasic
set_option autoImplicit true
open Psi

theorem Psi.numN_cons (a : Bool) (t : List Bool) :
    numN (a :: t) = (if a = true then 1 else 0) + numN t := by sorry
