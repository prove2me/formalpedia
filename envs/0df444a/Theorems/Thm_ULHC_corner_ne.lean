-- Prove2me | Theorems.Thm_ULHC_corner_ne
-- name    : ULHC.corner_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:36:59.175966+00:00
-- url     : https://prove2.me/theorems/e4362a86-5b30-4bbc-a1af-170b347bf34d
-- title:
--   ULHC: corner ne
-- statement:
--   The ULHC construction uses the corner ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L303-L307
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L303-L307

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)

theorem ULHC.corner_ne {m : ℕ} (h : m ≠ 0) :
    back1 c s ≠ front1 (cellJ c s m) s ∧ back1 c s ≠ front2 (cellJ c s m) s ∧
      front1 c s ≠ front1 (cellJ c s m) s ∧ front1 c s ≠ front2 (cellJ c s m) s := by sorry
