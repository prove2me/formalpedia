-- Prove2me | Theorems.Thm_ULHC_stepFlow_left
-- name    : ULHC.stepFlow_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:56:18.887442+00:00
-- url     : https://prove2.me/theorems/69bff06c-f27e-4ecf-ba5d-a27b45343875
-- title:
--   ULHC: step Flow left
-- statement:
--   The ULHC construction uses the step Flow left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Conn.lean#L100-L104
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Conn.lean#L100-L104

import Definitions.Def_ULHC_D
import Definitions.Def_ULHC_Conn
set_option autoImplicit true
open ULHC

theorem ULHC.stepFlow_left (u : Pt) :
    stepFlow u (u.1 - 1, u.2) = fun e => - oneE ⟨.h, (u.1 - 1, u.2)⟩ e := by sorry
