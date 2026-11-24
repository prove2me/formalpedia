-- Prove2me | Theorems.Thm_ULHC_not_mid_start
-- name    : ULHC.not_mid_start
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:50:12.911688+00:00
-- url     : https://prove2.me/theorems/d0b2e932-e8d1-4c84-a4fb-14bfa8388547
-- title:
--   ULHC: not mid start
-- statement:
--   The ULHC construction uses the not mid start property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/V2.lean#L49-L57
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/V2.lean#L49-L57

import Definitions.Def_ULHC_TheoremA
import Definitions.Def_ULHC_V2
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.not_mid_start (c : Pt) (s : Side) (k : ℕ) :
    ¬ IsMid c s k (back1 c s) ∧ ¬ IsMid c s k (front1 c s) := by sorry
