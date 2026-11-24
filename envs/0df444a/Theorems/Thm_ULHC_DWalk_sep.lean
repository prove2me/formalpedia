-- Prove2me | Theorems.Thm_ULHC_DWalk_sep
-- name    : ULHC.DWalk.sep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:45:21.513557+00:00
-- url     : https://prove2.me/theorems/da8bc44b-b421-42c5-9792-faffbaaa9f1c
-- title:
--   DWalk: sep
-- statement:
--   The DWalk construction uses the sep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Dual.lean#L143-L155
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Dual.lean#L143-L155

import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Dual
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge}

theorem ULHC.DWalk.sep (hs : Solid V) (hFV : Inside V F) (x0 : Pt)
    (hconn : ∀ z ∈ V, Conn (GE V) x0 z) {a : Pt} {B : Finset Edge} (h : DWalk V F a a B)
    {e : Edge} (he : e ∈ B) (hE : IsEdge V e) : ¬ Conn F e.p e.q := by sorry
