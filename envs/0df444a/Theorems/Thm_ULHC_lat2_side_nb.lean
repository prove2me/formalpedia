-- Prove2me | Theorems.Thm_ULHC_lat2_side_nb
-- name    : ULHC.lat2_side_nb
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:43:10.891927+00:00
-- url     : https://prove2.me/theorems/3bf53fa9-11e2-4cce-906f-eaae7d2dbbbf
-- title:
--   ULHC: lat2 side nb
-- statement:
--   The ULHC construction uses the lat2 side nb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L36-L37
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L36-L37

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)

theorem ULHC.lat2_side_nb : lat2 c s = sideEdge (nb c (latB s)) (latB s).opp := by sorry
