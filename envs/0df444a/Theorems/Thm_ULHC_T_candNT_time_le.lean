-- Prove2me | Theorems.Thm_ULHC_T_candNT_time_le
-- name    : ULHC.T.candNT_time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:15:02.057624+00:00
-- url     : https://prove2.me/theorems/7bc5f8ef-9ab3-41ef-9e60-e2b412ff5402
-- title:
--   T: cand NT time le
-- statement:
--   The T construction uses the cand NT time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/Strips.lean#L434-L447
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/Strips.lean#L434-L447

import Definitions.Def_ULHC_Timed_Conn
import Definitions.Def_ULHC_CostStrips
import Definitions.Def_ULHC_Timed_Strips
set_option autoImplicit true
open ULHC ULHC.T
open Finset

theorem ULHC.T.candNT_time_le (V : Finset Pt) (G : Finset Edge) : (candNT V G).time ≤ candNCost V G := by sorry
