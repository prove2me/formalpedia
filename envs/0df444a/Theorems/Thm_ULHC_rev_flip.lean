-- Prove2me | Theorems.Thm_ULHC_rev_flip
-- name    : ULHC.rev_flip
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:57:47.641576+00:00
-- url     : https://prove2.me/theorems/feb1d3c9-2f78-416c-8c16-5226d8369198
-- title:
--   ULHC: rev flip
-- statement:
--   The ULHC construction uses the rev flip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reverse.lean#L50-L54
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reverse.lean#L50-L54

import Definitions.Def_ULHC_NearLemma
import Definitions.Def_ULHC_Reverse
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.rev_flip (F : Finset Edge) (c : Pt) (s : Side) (k : ℕ) :
    flipCol (flipCol F c s (k + 2)) (cellJ c s (k + 1)) s.opp (k + 2) = F := by sorry
