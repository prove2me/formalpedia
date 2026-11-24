-- Prove2me | Theorems.Thm_ULHC_lat2_eq
-- name    : ULHC.lat2_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:20:27.334935+00:00
-- url     : https://prove2.me/theorems/b2eafcfb-a7d7-4bee-8c48-aebfcd9fa41c
-- title:
--   ULHC: lat2 eq
-- statement:
--   The ULHC construction uses the lat2 eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Walk.lean#L125-L125
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Walk.lean#L125-L125

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_Walk
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.lat2_eq (c : Pt) (s : Side) : lat2 c s = sideEdge c (latB s) := by sorry
