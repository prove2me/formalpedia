-- Prove2me | Theorems.Thm_ULHC_back_not_mem
-- name    : ULHC.back_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:31:55.310094+00:00
-- url     : https://prove2.me/theorems/f8fab138-439f-4743-93f1-3fff474a7714
-- title:
--   ULHC: back not mem
-- statement:
--   The ULHC construction uses the back not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L294-L296
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L294-L296

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)

theorem ULHC.back_not_mem {m : ℕ} (h : m ≠ 0) : back c s ∉ cellE (cellJ c s m) := by sorry
