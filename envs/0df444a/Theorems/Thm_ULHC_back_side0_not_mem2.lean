-- Prove2me | Theorems.Thm_ULHC_back_side0_not_mem2
-- name    : ULHC.back_side0_not_mem2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:01:01.056366+00:00
-- url     : https://prove2.me/theorems/0fdd6abf-7849-4520-878c-42bd32197cad
-- title:
--   ULHC: back side0 not mem2
-- statement:
--   The ULHC construction uses the back side0 not mem2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Complete.lean#L103-L105
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Complete.lean#L103-L105

import Definitions.Def_ULHC_Reverse
import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.back_side0_not_mem2 (c : Pt) (s : Side) (i : ℕ) :
    back (nb c (latB s)) s ∉ cellE (cellJ c s i) := by sorry
