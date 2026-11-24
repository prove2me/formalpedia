-- Prove2me | Theorems.Thm_ULHC_horiz_latA
-- name    : ULHC.horiz_latA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:41:44.633806+00:00
-- url     : https://prove2.me/theorems/537d1813-638f-4d5c-94f5-7e5a3f979c2c
-- title:
--   ULHC: horiz lat A
-- statement:
--   The ULHC construction uses the horiz lat A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Phase2.lean#L46-L46
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Phase2.lean#L46-L46

import Definitions.Def_ULHC_Phase
import Definitions.Def_ULHC_Phase2
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.horiz_latA (s : Side) : (latA s).horiz = !s.horiz := by sorry
