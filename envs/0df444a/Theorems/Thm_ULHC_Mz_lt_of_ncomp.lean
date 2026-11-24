-- Prove2me | Theorems.Thm_ULHC_Mz_lt_of_ncomp
-- name    : ULHC.Mz_lt_of_ncomp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:06:01.360802+00:00
-- url     : https://prove2.me/theorems/a0a3a63b-5986-44f4-b8ce-4485daa57ce0
-- title:
--   ULHC: Mz lt of ncomp
-- statement:
--   The ULHC construction uses the Mz lt of ncomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AlgComplete.lean#L155-L162
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AlgComplete.lean#L155-L162

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Counts
import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_AlgComplete
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt}

theorem ULHC.Mz_lt_of_ncomp {G G' : Finset Edge} (hG' : Inside V G')
    (h : ncomp V G' + 1 ≤ ncomp V G) : Mz V G' < Mz V G := by sorry
