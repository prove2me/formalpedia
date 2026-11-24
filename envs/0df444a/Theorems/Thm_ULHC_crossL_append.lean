-- Prove2me | Theorems.Thm_ULHC_crossL_append
-- name    : ULHC.crossL_append
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:54:01.258954+00:00
-- url     : https://prove2.me/theorems/d08d9de8-a1d8-4498-ae35-552b35ac1030
-- title:
--   ULHC: cross L append
-- statement:
--   The ULHC construction uses the cross L append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L528-L539
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L528-L539

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

theorem ULHC.crossL_append (B : Finset Edge) (u : Pt) (l : List Pt) (d : Pt) :
    crossL B u (l ++ [d]) =
      crossL B u l + (if ∃ e ∈ B, Ends e ((u :: l).getLast (by simp)) d then 1 else 0) := by sorry
