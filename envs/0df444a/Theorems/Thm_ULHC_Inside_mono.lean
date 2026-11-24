-- Prove2me | Theorems.Thm_ULHC_Inside_mono
-- name    : ULHC.Inside.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:44:49.381967+00:00
-- url     : https://prove2.me/theorems/d233e13b-3b4f-4a1e-8cdd-8e30f4594dd6
-- title:
--   Inside: mono
-- statement:
--   The Inside construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L304-L305
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L304-L305

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
import Theorems.Thm_ULHC_Adj_mono
import Theorems.Thm_ULHC_Conn_mono

set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.Inside.mono {V : Finset Pt} {F F' : Finset Edge} (h : Inside V F) (hs : F' ⊆ F) :
    Inside V F' := by sorry
