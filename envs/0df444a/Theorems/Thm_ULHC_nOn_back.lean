-- Prove2me | Theorems.Thm_ULHC_nOn_back
-- name    : ULHC.nOn_back
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:41:20.29731+00:00
-- url     : https://prove2.me/theorems/faba9175-84cc-456a-92b8-0dd51b0bda2c
-- title:
--   ULHC: n On back
-- statement:
--   The ULHC construction uses the n On back property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L757-L765
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L757-L765

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)

theorem ULHC.nOn_back {n : ℕ} (hn : 1 ≤ n) : nOn c s n (back c s) = 1 := by sorry
