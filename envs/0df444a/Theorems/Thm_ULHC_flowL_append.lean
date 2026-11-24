-- Prove2me | Theorems.Thm_ULHC_flowL_append
-- name    : ULHC.flowL_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:41.512361+00:00
-- url     : https://prove2.me/theorems/e80678d9-1290-45ea-b329-110059ab2c5f
-- title:
--   ULHC: flow L append
-- statement:
--   The ULHC construction uses the flow L append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Planar.lean#L50-L56
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Planar.lean#L50-L56

import Definitions.Def_ULHC_Conn
import Definitions.Def_ULHC_Planar
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
open Finset

theorem ULHC.flowL_append (u : Pt) (l₁ l₂ : List Pt) (e : Edge) :
    flowL u (l₁ ++ l₂) e = flowL u l₁ e + flowL ((u :: l₁).getLast (by simp)) l₂ e := by sorry
