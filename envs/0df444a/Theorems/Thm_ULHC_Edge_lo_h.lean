-- Prove2me | Theorems.Thm_ULHC_Edge_lo_h
-- name    : ULHC.Edge.lo_h
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:36:14.718643+00:00
-- url     : https://prove2.me/theorems/d406d4c3-2444-443c-a812-f98620c39953
-- title:
--   Edge: lo h
-- statement:
--   The Edge construction uses the lo h property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Grid.lean#L124-L124
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Grid.lean#L124-L124

import Mathlib
import Definitions.Def_ULHC_Grid
set_option autoImplicit true
open ULHC

theorem ULHC.Edge.lo_h (p : Pt) : (Edge.mk .h p).lo = (p.1, p.2 - 1) := by sorry

attribute [defeq] ULHC.Edge.lo_h
