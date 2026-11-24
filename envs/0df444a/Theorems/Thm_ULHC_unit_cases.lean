-- Prove2me | Theorems.Thm_ULHC_unit_cases
-- name    : ULHC.unit_cases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:50:43.264296+00:00
-- url     : https://prove2.me/theorems/644ae472-3493-4c4c-a057-6c89a9acf0cd
-- title:
--   ULHC: unit cases
-- statement:
--   The ULHC construction uses the unit cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Conn.lean#L82-L89
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Conn.lean#L82-L89

import Definitions.Def_ULHC_D
import Definitions.Def_ULHC_Conn
set_option autoImplicit true
open ULHC

theorem ULHC.unit_cases {u v : Pt} (h : Unit u v) :
    v = (u.1 + 1, u.2) ∨ v = (u.1 - 1, u.2) ∨ v = (u.1, u.2 + 1) ∨ v = (u.1, u.2 - 1) := by sorry
