-- Prove2me | Theorems.Thm_ULHC_sideEdge_nb_opp
-- name    : ULHC.sideEdge_nb_opp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:48:05.334017+00:00
-- url     : https://prove2.me/theorems/46815ba7-c151-4a55-8fdc-ba9dc452dad9
-- title:
--   ULHC: side Edge nb opp
-- statement:
--   The ULHC construction uses the side Edge nb opp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Phase.lean#L23-L24
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Phase.lean#L23-L24

import Definitions.Def_ULHC_Walk
import Definitions.Def_ULHC_Phase
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.sideEdge_nb_opp (c : Pt) (s : Side) : sideEdge (nb c s) s.opp = sideEdge c s := by sorry
