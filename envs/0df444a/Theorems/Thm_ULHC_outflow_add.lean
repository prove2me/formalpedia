-- Prove2me | Theorems.Thm_ULHC_outflow_add
-- name    : ULHC.outflow_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:51:39.299751+00:00
-- url     : https://prove2.me/theorems/40a3f90c-8717-42ca-a2e6-52fe386958a7
-- title:
--   ULHC: outflow add
-- statement:
--   The ULHC construction uses the outflow add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Conn.lean#L149-L151
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Conn.lean#L149-L151

import Definitions.Def_ULHC_D
import Definitions.Def_ULHC_Conn
set_option autoImplicit true
open ULHC

theorem ULHC.outflow_add (f g : Edge → ℤ) (x : Pt) :
    outflow (fun e => f e + g e) x = outflow f x + outflow g x := by sorry
