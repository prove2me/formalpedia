-- Prove2me | Theorems.Thm_ULHC_preach_chain
-- name    : ULHC.preach_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:55:27.941378+00:00
-- url     : https://prove2.me/theorems/a0bdc543-09b8-4e7b-aba5-b5632679a6fd
-- title:
--   ULHC: preach chain
-- statement:
--   The ULHC construction uses the preach chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L588-L611
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L588-L611

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v


set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} (B : Finset Edge)

theorem ULHC.preach_chain {a c : Pt} {b b' : Bool}
    (h : Relation.ReflTransGen (PStep V B) (a, b) (c, b')) :
    ∃ l, List.IsChain (Adj (GE V)) (a :: l) ∧ (a :: l).getLast (by simp) = c ∧
      (crossL B a l % 2 = if b = b' then 0 else 1) := by sorry
