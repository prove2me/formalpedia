-- Prove2me | Theorems.Thm_ULHC_preach_neg
-- name    : ULHC.preach_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:55:12.906003+00:00
-- url     : https://prove2.me/theorems/ca18d149-83f0-499a-bcc4-0e3d4c9bb931
-- title:
--   ULHC: preach neg
-- statement:
--   The ULHC construction uses the preach neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L582-L586
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L582-L586

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} (B : Finset Edge)

theorem ULHC.preach_neg {x y : Pt × Bool} (h : Relation.ReflTransGen (PStep V B) x y) :
    Relation.ReflTransGen (PStep V B) (x.1, !x.2) (y.1, !y.2) := by sorry
