-- Prove2me | Theorems.Thm_ULHC_outflow_oneE_v
-- name    : ULHC.outflow_oneE_v
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:56:20.965971+00:00
-- url     : https://prove2.me/theorems/a5b4097b-fca2-4d3b-9731-9a43001a29e6
-- title:
--   ULHC: outflow one E v
-- statement:
--   The ULHC construction uses the outflow one E v property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Conn.lean#L126-L133
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Conn.lean#L126-L133

import Definitions.Def_ULHC_D
import Definitions.Def_ULHC_Conn
set_option autoImplicit true
open ULHC

theorem ULHC.outflow_oneE_v (a : Pt) (x : Pt) :
    outflow (oneE ⟨.v, a⟩) x = (if x = a then 1 else 0) - (if x = (a.1, a.2 + 1) then 1 else 0) := by sorry
