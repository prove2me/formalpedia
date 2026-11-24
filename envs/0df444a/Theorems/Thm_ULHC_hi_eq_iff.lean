-- Prove2me | Theorems.Thm_ULHC_hi_eq_iff
-- name    : ULHC.hi_eq_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:43:32.744257+00:00
-- url     : https://prove2.me/theorems/3f4c0432-c19c-4f0a-aa5b-3c2c447e2415
-- title:
--   ULHC: hi eq iff
-- statement:
--   The ULHC construction uses the hi eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L337-L339
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L337-L339

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.hi_eq_iff (e : Edge) (c : Pt) : e.hi = c ↔ (e = bot c ∨ e = lft c) := by sorry
