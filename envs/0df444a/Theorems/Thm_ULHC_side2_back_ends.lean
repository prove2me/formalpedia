-- Prove2me | Theorems.Thm_ULHC_side2_back_ends
-- name    : ULHC.side2_back_ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:20:15.02154+00:00
-- url     : https://prove2.me/theorems/4256eed5-67ee-46f7-89b5-09842606b023
-- title:
--   ULHC: side2 back ends
-- statement:
--   The ULHC construction uses the side2 back ends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Near.lean#L72-L74
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Near.lean#L72-L74

import Definitions.Def_ULHC_Enum
import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Near
set_option autoImplicit true
open ULHC
open Finset
variable (c : Pt) (s : Side)

theorem ULHC.side2_back_ends : Ends (back (nb c (latB s)) s) (back2 c s) (back2 (nb c (latB s)) s) := by sorry
