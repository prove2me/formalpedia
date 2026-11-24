-- Prove2me | Theorems.Thm_ULHC_Mz_of_T3
-- name    : ULHC.Mz_of_T3
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:06:29.442466+00:00
-- url     : https://prove2.me/theorems/4686939e-bc7e-4d41-807f-2b44f9de9ed1
-- title:
--   ULHC: Mz of T3
-- statement:
--   The ULHC construction uses the Mz of T3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AlgComplete.lean#L169-L172
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AlgComplete.lean#L169-L172

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Counts
import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_AlgComplete
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt}

theorem ULHC.Mz_of_T3 {G : Finset Edge} (hT : ¬ NoTypeIII V G) :
    Mz V G = ncomp V G * (2 * Dm V + 4) + 1 := by sorry
