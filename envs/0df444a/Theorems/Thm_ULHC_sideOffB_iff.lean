-- Prove2me | Theorems.Thm_ULHC_sideOffB_iff
-- name    : ULHC.sideOffB_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:51:58.176269+00:00
-- url     : https://prove2.me/theorems/66f1affe-38d6-474b-b218-50408aa0d0c2
-- title:
--   ULHC: side Off B iff
-- statement:
--   The ULHC construction uses the side Off B iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Enum.lean#L213-L217
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Enum.lean#L213-L217

import Definitions.Def_ULHC_CrPath
import Definitions.Def_ULHC_Comp
import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_Enum
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F G : Finset Edge}

theorem ULHC.sideOffB_iff {b c : StripSpec} : sideOffB b c = true ↔ SideOff b c := by sorry
