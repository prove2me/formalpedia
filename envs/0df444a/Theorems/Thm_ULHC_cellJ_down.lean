-- Prove2me | Theorems.Thm_ULHC_cellJ_down
-- name    : ULHC.cellJ_down
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:21:42.60088+00:00
-- url     : https://prove2.me/theorems/574a46f8-71b6-4e45-b19d-da8e77674fe5
-- title:
--   ULHC: cell J down
-- statement:
--   The ULHC construction uses the cell J down property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearLemma.lean#L91-L92
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearLemma.lean#L91-L92

import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.cellJ_down (c : Pt) (s : Side) (j : ℕ) : nb (cellJ c s (j + 1)) s.opp = cellJ c s j := by sorry
