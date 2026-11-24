-- Prove2me | Theorems.Thm_ULHC_extra_le
-- name    : ULHC.extra_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:38:43.944805+00:00
-- url     : https://prove2.me/theorems/284d5ce3-69d8-4d3d-8abd-d20766ac3472
-- title:
--   ULHC: extra le
-- statement:
--   The ULHC construction uses the extra le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AlgComplete.lean#L143-L147
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AlgComplete.lean#L143-L147

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Counts
import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_AlgComplete
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt}

theorem ULHC.extra_le {G : Finset Edge} (hGV : Inside V G) :
    Mz V G ≤ ncomp V G * (2 * Dm V + 4) + (2 * Dm V + 2) := by sorry
