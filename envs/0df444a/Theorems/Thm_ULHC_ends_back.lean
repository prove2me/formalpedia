-- Prove2me | Theorems.Thm_ULHC_ends_back
-- name    : ULHC.ends_back
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:46:16.519769+00:00
-- url     : https://prove2.me/theorems/13c62bfd-c078-494d-8fa0-8705cc952721
-- title:
--   ULHC: ends back
-- statement:
--   The ULHC construction uses the ends back property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Strip.lean#L115-L117
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Strip.lean#L115-L117

import Definitions.Def_ULHC_Iso
import Definitions.Def_ULHC_Strip
set_option autoImplicit true
open ULHC
open Finset
variable (c : Pt) (s : Side)

theorem ULHC.ends_back : Ends (back c s) (back1 c s) (back2 c s) := by sorry
