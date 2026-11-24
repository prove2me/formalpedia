-- Prove2me | Theorems.Thm_ULHC_lo_eq_iff
-- name    : ULHC.lo_eq_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:42:55.856796+00:00
-- url     : https://prove2.me/theorems/36211839-a631-49b6-9eb5-7dbbda76eed9
-- title:
--   ULHC: lo eq iff
-- statement:
--   The ULHC construction uses the lo eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L341-L344
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L341-L344

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.lo_eq_iff (e : Edge) (c : Pt) : e.lo = c ↔ (e = top c ∨ e = rgt c) := by sorry
