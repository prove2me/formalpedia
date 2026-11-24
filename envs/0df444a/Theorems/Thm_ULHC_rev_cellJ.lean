-- Prove2me | Theorems.Thm_ULHC_rev_cellJ
-- name    : ULHC.rev_cellJ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:22:20.0418+00:00
-- url     : https://prove2.me/theorems/6d635bcb-6f6c-437e-8807-b82fb8397222
-- title:
--   ULHC: rev cell J
-- statement:
--   The ULHC construction uses the rev cell J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reverse.lean#L27-L30
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reverse.lean#L27-L30

import Definitions.Def_ULHC_NearLemma
import Definitions.Def_ULHC_Reverse
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.rev_cellJ (c : Pt) (s : Side) {i k : ℕ} (hi : i ≤ k + 1) :
    cellJ (cellJ c s (k + 1)) s.opp i = cellJ c s (k + 1 - i) := by sorry
