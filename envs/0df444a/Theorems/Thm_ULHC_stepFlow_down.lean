-- Prove2me | Theorems.Thm_ULHC_stepFlow_down
-- name    : ULHC.stepFlow_down
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:56:20.52682+00:00
-- url     : https://prove2.me/theorems/b102cb78-135f-4ec6-9c13-f927f0a5140b
-- title:
--   ULHC: step Flow down
-- statement:
--   The ULHC construction uses the step Flow down property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Conn.lean#L111-L115
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Conn.lean#L111-L115

import Definitions.Def_ULHC_D
import Definitions.Def_ULHC_Conn
set_option autoImplicit true
open ULHC

theorem ULHC.stepFlow_down (u : Pt) :
    stepFlow u (u.1, u.2 - 1) = fun e => - oneE ⟨.v, (u.1, u.2 - 1)⟩ e := by sorry
