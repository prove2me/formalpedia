-- Prove2me | Theorems.Thm_ULHC_frame_opp
-- name    : ULHC.frame_opp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:59:18.273193+00:00
-- url     : https://prove2.me/theorems/2b447c5e-a415-4a78-bb6e-6c32bbcf3dc4
-- title:
--   ULHC: frame opp
-- statement:
--   The ULHC construction uses the frame opp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean#L30-L34
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean#L30-L34

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Touch
set_option autoImplicit true
open ULHC
open Finset
variable (d : Pt) (s : Side)

theorem ULHC.frame_opp : lat1 d s.opp = lat1 d s ∧ lat2 d s.opp = lat2 d s ∧
    back d s.opp = front d s ∧ front d s.opp = back d s := by sorry
