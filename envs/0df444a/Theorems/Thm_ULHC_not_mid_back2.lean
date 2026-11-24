-- Prove2me | Theorems.Thm_ULHC_not_mid_back2
-- name    : ULHC.not_mid_back2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:50:13.45549+00:00
-- url     : https://prove2.me/theorems/3554c2f9-09e0-4b59-a337-c7b1fd69da8b
-- title:
--   ULHC: not mid back2
-- statement:
--   The ULHC construction uses the not mid back2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/V2.lean#L45-L47
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/V2.lean#L45-L47

import Definitions.Def_ULHC_TheoremA
import Definitions.Def_ULHC_V2
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.not_mid_back2 (c : Pt) (s : Side) (k : ℕ) : ¬ IsMid c s k (back2 c s) := by sorry
