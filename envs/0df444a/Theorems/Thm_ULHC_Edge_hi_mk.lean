-- Prove2me | Theorems.Thm_ULHC_Edge_hi_mk
-- name    : ULHC.Edge.hi_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:36:16.521069+00:00
-- url     : https://prove2.me/theorems/aaee199d-c692-425f-8728-208fae64b3b3
-- title:
--   Edge: hi mk
-- statement:
--   The Edge construction uses the hi mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Grid.lean#L123-L123
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Grid.lean#L123-L123

import Mathlib
import Definitions.Def_ULHC_Grid
set_option autoImplicit true
open ULHC

theorem ULHC.Edge.hi_mk (d : Dir) (p : Pt) : (Edge.mk d p).hi = p := by sorry

attribute [defeq] ULHC.Edge.hi_mk
