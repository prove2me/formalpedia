-- Prove2me | Theorems.Thm_ULHC_side_back_next
-- name    : ULHC.side_back_next
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:27:27.790617+00:00
-- url     : https://prove2.me/theorems/349c2b7d-b71f-47d5-9bf3-06f60756d8c3
-- title:
--   ULHC: side back next
-- statement:
--   The ULHC construction uses the side back next property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L82-L83
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L82-L83

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)

theorem ULHC.side_back_next : back (nb (nb c s) (latA s)) s = outer1 c s := by sorry
