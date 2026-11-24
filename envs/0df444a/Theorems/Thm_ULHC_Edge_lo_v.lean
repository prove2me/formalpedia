-- Prove2me | Theorems.Thm_ULHC_Edge_lo_v
-- name    : ULHC.Edge.lo_v
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:36:17.363005+00:00
-- url     : https://prove2.me/theorems/b4dc5481-cb54-4b2c-8fce-4adfc395e2e1
-- title:
--   Edge: lo v
-- statement:
--   The Edge construction uses the lo v property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Grid.lean#L125-L125
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Grid.lean#L125-L125

import Mathlib
import Definitions.Def_ULHC_Grid
set_option autoImplicit true
open ULHC

theorem ULHC.Edge.lo_v (p : Pt) : (Edge.mk .v p).lo = (p.1 - 1, p.2) := by sorry

attribute [defeq] ULHC.Edge.lo_v
