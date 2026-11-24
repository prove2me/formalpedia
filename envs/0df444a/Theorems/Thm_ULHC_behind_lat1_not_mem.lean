-- Prove2me | Theorems.Thm_ULHC_behind_lat1_not_mem
-- name    : ULHC.behind_lat1_not_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:00:19.015905+00:00
-- url     : https://prove2.me/theorems/8637a0ea-b1f0-4419-bc2c-402205650fb8
-- title:
--   ULHC: behind lat1 not mem
-- statement:
--   The ULHC construction uses the behind lat1 not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Complete.lean#L56-L58
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Complete.lean#L56-L58

import Definitions.Def_ULHC_Reverse
import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.behind_lat1_not_mem (c : Pt) (s : Side) (j : ℕ) :
    lat1 (nb c s.opp) s ∉ cellE (cellJ c s j) := by sorry
