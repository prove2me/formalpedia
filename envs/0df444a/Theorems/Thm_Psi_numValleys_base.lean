-- Prove2me | Theorems.Thm_Psi_numValleys_base
-- name    : Psi.numValleys_base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:09:49.344807+00:00
-- url     : https://prove2.me/theorems/f59b3b8c-a7c6-42ff-b088-cdf9e9f1477e
-- title:
--   Psi: num Valleys base
-- statement:
--   The Psi construction uses the num Valleys base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L448-L457
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L448-L457

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.numValleys_base (l k : Nat) :
    numValleys ((List.replicate l [true, false]).flatten ++ List.replicate (k+1) true
      ++ List.replicate (k+1) false) = l := by sorry
