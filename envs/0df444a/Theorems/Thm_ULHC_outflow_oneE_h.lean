-- Prove2me | Theorems.Thm_ULHC_outflow_oneE_h
-- name    : ULHC.outflow_oneE_h
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:56:25.234557+00:00
-- url     : https://prove2.me/theorems/be158087-6c40-4259-b9c1-aa4ab4c8a5b2
-- title:
--   ULHC: outflow one E h
-- statement:
--   The ULHC construction uses the outflow one E h property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Conn.lean#L117-L124
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Conn.lean#L117-L124

import Definitions.Def_ULHC_D
import Definitions.Def_ULHC_Conn
set_option autoImplicit true
open ULHC

theorem ULHC.outflow_oneE_h (a : Pt) (x : Pt) :
    outflow (oneE ⟨.h, a⟩) x = (if x = a then 1 else 0) - (if x = (a.1 + 1, a.2) then 1 else 0) := by sorry
