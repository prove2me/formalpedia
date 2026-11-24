-- Prove2me | Theorems.Thm_ULHC_stepFlow_ne_zero
-- name    : ULHC.stepFlow_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:42:05.499802+00:00
-- url     : https://prove2.me/theorems/4cfc6057-ebb4-44d9-a6ec-8506a76fcbda
-- title:
--   ULHC: step Flow ne zero
-- statement:
--   The ULHC construction uses the step Flow ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Planar.lean#L30-L36
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Planar.lean#L30-L36

import Definitions.Def_ULHC_Conn
import Definitions.Def_ULHC_Planar
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.stepFlow_ne_zero {u v : Pt} {e : Edge} (h : stepFlow u v e ≠ 0) :
    (e.p = u ∧ e.q = v) ∨ (e.p = v ∧ e.q = u) := by sorry
