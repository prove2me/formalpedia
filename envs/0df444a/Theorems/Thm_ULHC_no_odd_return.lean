-- Prove2me | Theorems.Thm_ULHC_no_odd_return
-- name    : ULHC.no_odd_return
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:40:51.30912+00:00
-- url     : https://prove2.me/theorems/5a200317-94a9-4e52-b8e1-0ae7e64e329f
-- title:
--   ULHC: no odd return
-- statement:
--   The ULHC construction uses the no odd return property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L624-L629
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L624-L629

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} (B : Finset Edge)
variable (hs : Solid V) (heven : ∀ c, IsCell V c → sidesIn B c % 2 = 0)
include hs heven

theorem ULHC.no_odd_return {a : Pt} {b : Bool} :
    ¬ Relation.ReflTransGen (PStep V B) (a, b) (a, !b) := by sorry
