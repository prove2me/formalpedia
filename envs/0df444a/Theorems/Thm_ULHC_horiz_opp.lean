-- Prove2me | Theorems.Thm_ULHC_horiz_opp
-- name    : ULHC.horiz_opp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:48:39.374703+00:00
-- url     : https://prove2.me/theorems/d6151670-abd7-4440-90db-76289125707f
-- title:
--   ULHC: horiz opp
-- statement:
--   The ULHC construction uses the horiz opp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Phase2.lean#L45-L45
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Phase2.lean#L45-L45

import Definitions.Def_ULHC_Phase
import Definitions.Def_ULHC_Phase2
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.horiz_opp (s : Side) : s.opp.horiz = s.horiz := by sorry
