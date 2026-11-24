-- Prove2me | Theorems.Thm_ULHC_frame_latA
-- name    : ULHC.frame_latA
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:59:25.932096+00:00
-- url     : https://prove2.me/theorems/49514026-6be7-4c2f-88e4-f2763d6bb821
-- title:
--   ULHC: frame lat A
-- statement:
--   The ULHC construction uses the frame lat A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean#L36-L42
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean#L36-L42

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Touch
set_option autoImplicit true
open ULHC
open Finset
variable (d : Pt) (s : Side)

theorem ULHC.frame_latA : front d (latA s) = lat1 d s ∧ back d (latA s) = lat2 d s ∧
    ((lat1 d (latA s) = back d s ∧ lat2 d (latA s) = front d s) ∨
      (lat1 d (latA s) = front d s ∧ lat2 d (latA s) = back d s)) := by sorry
