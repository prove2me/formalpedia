-- Prove2me | Theorems.Thm_ULHC_outflow_neg
-- name    : ULHC.outflow_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:56:27.616802+00:00
-- url     : https://prove2.me/theorems/077cd96c-bdd6-48a1-875a-4a19f8953da6
-- title:
--   ULHC: outflow neg
-- statement:
--   The ULHC construction uses the outflow neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Conn.lean#L135-L136
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Conn.lean#L135-L136

import Definitions.Def_ULHC_D
import Definitions.Def_ULHC_Conn
set_option autoImplicit true
open ULHC

theorem ULHC.outflow_neg (f : Edge → ℤ) (x : Pt) : outflow (fun e => - f e) x = - outflow f x := by sorry
