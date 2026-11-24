-- Prove2me | Theorems.Thm_ULHC_bool_not_iff
-- name    : ULHC.bool_not_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:56:53.743638+00:00
-- url     : https://prove2.me/theorems/17f63e50-4d0e-4cf4-8855-c22131bcd494
-- title:
--   ULHC: bool not iff
-- statement:
--   The ULHC construction uses the bool not iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Enum.lean#L243-L244
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Enum.lean#L243-L244

import Definitions.Def_ULHC_CrPath
import Definitions.Def_ULHC_Comp
import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_Enum
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F G : Finset Edge}

theorem ULHC.bool_not_iff {p : Bool} {P : Prop} (h : p = true ↔ P) : (!p) = true ↔ ¬ P := by sorry
