-- Prove2me | Theorems.Thm_ULHC_back_cellJ_succ
-- name    : ULHC.back_cellJ_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:19:22.107995+00:00
-- url     : https://prove2.me/theorems/7efd7979-036d-4f10-8ed3-3af0c4ac88e1
-- title:
--   ULHC: back cell J succ
-- statement:
--   The ULHC construction uses the back cell J succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L298-L299
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L298-L299

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)

theorem ULHC.back_cellJ_succ (j : ℕ) : back (cellJ c s (j + 1)) s = front (cellJ c s j) s := by sorry
