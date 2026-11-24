-- Prove2me | Theorems.Thm_ULHC_cellE_frame
-- name    : ULHC.cellE_frame
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:18:57.219322+00:00
-- url     : https://prove2.me/theorems/102c536f-e30e-4058-92b5-02137be6d901
-- title:
--   ULHC: cell E frame
-- statement:
--   The ULHC construction uses the cell E frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L38-L42
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L38-L42

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.cellE_frame (c : Pt) (s : Side) :
    cellE c = {back c s, front c s, lat1 c s, lat2 c s} := by sorry
