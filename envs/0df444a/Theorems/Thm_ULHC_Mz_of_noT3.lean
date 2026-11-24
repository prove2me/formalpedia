-- Prove2me | Theorems.Thm_ULHC_Mz_of_noT3
-- name    : ULHC.Mz_of_noT3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:06:18.780441+00:00
-- url     : https://prove2.me/theorems/496a5935-7606-4378-bb96-8328da8982ed
-- title:
--   ULHC: Mz of no T3
-- statement:
--   The ULHC construction uses the Mz of no T3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AlgComplete.lean#L164-L167
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AlgComplete.lean#L164-L167

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Counts
import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_AlgComplete
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt}

theorem ULHC.Mz_of_noT3 {G : Finset Edge} (hT : NoTypeIII V G) :
    Mz V G = ncomp V G * (2 * Dm V + 4) + (2 * dval V G + 2) := by sorry
