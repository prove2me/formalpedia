-- Prove2me | Theorems.Thm_ULHC_outflow_flowL
-- name    : ULHC.outflow_flowL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:51:58.204355+00:00
-- url     : https://prove2.me/theorems/f4061ff0-1091-474c-b67a-4bd7299ec677
-- title:
--   ULHC: outflow flow L
-- statement:
--   The ULHC construction uses the outflow flow L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Conn.lean#L155-L167
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Conn.lean#L155-L167

import Definitions.Def_ULHC_D
import Definitions.Def_ULHC_Conn
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

theorem ULHC.outflow_flowL (u : Pt) (l : List Pt) (hc : List.IsChain Unit (u :: l)) (x : Pt) :
    outflow (flowL u l) x =
      (if x = u then 1 else 0) - (if x = (u :: l).getLast (by simp) then 1 else 0) := by sorry
