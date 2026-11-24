-- Prove2me | Theorems.Thm_ULHC_wD_flip_off
-- name    : ULHC.wD_flip_off
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:55:55.935233+00:00
-- url     : https://prove2.me/theorems/98474f78-fb4a-4de3-90e1-b91802261e0d
-- title:
--   ULHC: w D flip off
-- statement:
--   The ULHC construction uses the w D flip off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/D.lean#L226-L230
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/D.lean#L226-L230

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.wD_flip_off {F H : Finset Edge} {c : Pt} {e : Edge} (he : e ∉ cellE c) :
    wD (flip F c) H e = wD F H e := by sorry
