-- Prove2me | Theorems.Thm_ULHC_pair_cells
-- name    : ULHC.pair_cells
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:47:30.689952+00:00
-- url     : https://prove2.me/theorems/1ebacc7f-cb5f-483d-ac55-2ba8d7f4f40c
-- title:
--   ULHC: pair cells
-- statement:
--   The ULHC construction uses the pair cells property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L239-L249
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L239-L249

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.pair_cells (c : Pt) (s : Side) :
    symmDiff (cellE (nb c s)) (cellE c) =
      {back c s, lat1 c s, lat2 c s, front (nb c s) s, lat1 (nb c s) s, lat2 (nb c s) s} := by sorry
