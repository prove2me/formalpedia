-- Prove2me | Theorems.Thm_ULHC_end_not_mid
-- name    : ULHC.end_not_mid
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:38:13.764554+00:00
-- url     : https://prove2.me/theorems/ab68bf91-703a-477d-b007-a65b6fd59f61
-- title:
--   ULHC: end not mid
-- statement:
--   The ULHC construction uses the end not mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/V2.lean#L34-L43
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/V2.lean#L34-L43

import Definitions.Def_ULHC_TheoremA
import Definitions.Def_ULHC_V2
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.end_not_mid (c : Pt) (s : Side) (k : ℕ) :
    ¬ IsMid c s k (back1 (cellJ c s (k + 1)) s) ∧ ¬ IsMid c s k (front1 (cellJ c s (k + 1)) s) := by sorry
