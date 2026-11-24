-- Prove2me | Theorems.Thm_ULHC_rev_cellJ_add
-- name    : ULHC.rev_cellJ_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:57:17.212109+00:00
-- url     : https://prove2.me/theorems/2b88c8ad-d09a-4a99-bc97-5d5d270fa4e3
-- title:
--   ULHC: rev cell J add
-- statement:
--   The ULHC construction uses the rev cell J add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reverse.lean#L22-L25
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reverse.lean#L22-L25

import Definitions.Def_ULHC_NearLemma
import Definitions.Def_ULHC_Reverse
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.rev_cellJ_add (c : Pt) (s : Side) (i m : ℕ) :
    cellJ (cellJ c s (i + m)) s.opp i = cellJ c s m := by sorry
