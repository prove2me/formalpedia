-- Prove2me | Theorems.Thm_Psi_numValleys_construction
-- name    : Psi.numValleys_construction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:09:43.662525+00:00
-- url     : https://prove2.me/theorems/6e34f652-e364-44c4-8281-65724b920e5e
-- title:
--   Psi: num Valleys construction
-- statement:
--   The Psi construction uses the num Valleys construction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L419-L447
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L419-L447

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.numValleys_construction (a b : Nat) (rho rho' : List Bool) (hb : 1 ≤ b)
    (hbd : stEast rho false = false → rho'.head? = some true) :
    numValleys (fUD a ++ [true] ++ rho ++ List.replicate b true
        ++ List.replicate (b+1) false ++ rho')
      = a + 1 + numValleys (rho ++ rho') := by sorry
