-- Prove2me | Theorems.Thm_ULHC_lat1_side_nb
-- name    : ULHC.lat1_side_nb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:39:21.589187+00:00
-- url     : https://prove2.me/theorems/8033a687-223e-4137-8a32-f19adcbb1f72
-- title:
--   ULHC: lat1 side nb
-- statement:
--   The ULHC construction uses the lat1 side nb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L33-L34
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L33-L34

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)

theorem ULHC.lat1_side_nb : lat1 c s = sideEdge (nb c (latA s)) (latA s).opp := by sorry
