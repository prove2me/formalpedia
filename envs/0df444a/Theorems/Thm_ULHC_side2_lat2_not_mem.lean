-- Prove2me | Theorems.Thm_ULHC_side2_lat2_not_mem
-- name    : ULHC.side2_lat2_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:32:05.846515+00:00
-- url     : https://prove2.me/theorems/653f6337-39ff-4798-ac48-cba5cfc089f4
-- title:
--   ULHC: side2 lat2 not mem
-- statement:
--   The ULHC construction uses the side2 lat2 not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Near.lean#L278-L281
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Near.lean#L278-L281

import Definitions.Def_ULHC_Enum
import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Near
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.side2_lat2_not_mem (c : Pt) (s : Side) (j m : ℕ) :
    lat2 (nb (cellJ c s j) (latB s)) s ∉ cellE (cellJ c s m) := by sorry
