-- Prove2me | Theorems.Thm_ULHC_frame_latB
-- name    : ULHC.frame_latB
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:59:05.696131+00:00
-- url     : https://prove2.me/theorems/1d42ac53-2297-477f-8435-03868598bb62
-- title:
--   ULHC: frame lat B
-- statement:
--   The ULHC construction uses the frame lat B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean#L44-L50
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean#L44-L50

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Touch
set_option autoImplicit true
open ULHC
open Finset
variable (d : Pt) (s : Side)

theorem ULHC.frame_latB : front d (latB s) = lat2 d s ∧ back d (latB s) = lat1 d s ∧
    ((lat1 d (latB s) = back d s ∧ lat2 d (latB s) = front d s) ∨
      (lat1 d (latB s) = front d s ∧ lat2 d (latB s) = back d s)) := by sorry
