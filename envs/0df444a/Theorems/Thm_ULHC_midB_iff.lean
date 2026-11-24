-- Prove2me | Theorems.Thm_ULHC_midB_iff
-- name    : ULHC.midB_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:51:59.863808+00:00
-- url     : https://prove2.me/theorems/c1edab3b-bc61-447a-a346-c3cfea41a63d
-- title:
--   ULHC: mid B iff
-- statement:
--   The ULHC construction uses the mid B iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Enum.lean#L223-L227
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Enum.lean#L223-L227

import Definitions.Def_ULHC_CrPath
import Definitions.Def_ULHC_Comp
import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_Enum
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F G : Finset Edge}

theorem ULHC.midB_iff {b : StripSpec} {z : Pt} : midB b z = true ↔ IsMid b.c b.s (b.n - 2) z := by sorry
