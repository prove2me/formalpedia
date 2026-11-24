-- Prove2me | Theorems.Thm_ULHC_nOn_rev
-- name    : ULHC.nOn_rev
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:57:41.404611+00:00
-- url     : https://prove2.me/theorems/a28f7dbb-1875-4ad9-a260-9fda2dbbdf39
-- title:
--   ULHC: n On rev
-- statement:
--   The ULHC construction uses the n On rev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reverse.lean#L32-L48
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reverse.lean#L32-L48

import Definitions.Def_ULHC_NearLemma
import Definitions.Def_ULHC_Reverse
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.nOn_rev (c : Pt) (s : Side) (k : ℕ) (x : Edge) :
    nOn (cellJ c s (k + 1)) s.opp (k + 2) x = nOn c s (k + 2) x := by sorry
