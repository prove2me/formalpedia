-- Prove2me | Theorems.Thm_ULHC_lat1_mem_self
-- name    : ULHC.lat1_mem_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:31:49.767713+00:00
-- url     : https://prove2.me/theorems/8f02941a-4459-4564-bb9a-c0e2f90511b2
-- title:
--   ULHC: lat1 mem self
-- statement:
--   The ULHC construction uses the lat1 mem self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L288-L289
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L288-L289

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)

theorem ULHC.lat1_mem_self (j : ℕ) : lat1 (cellJ c s j) s ∈ cellE (cellJ c s j) := by sorry
