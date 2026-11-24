-- Prove2me | Theorems.Thm_ULHC_DWalk_sep_ends
-- name    : ULHC.DWalk.sep_ends
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:44:36.005637+00:00
-- url     : https://prove2.me/theorems/02214edc-c487-40a7-b874-c04ba5070d45
-- title:
--   DWalk: sep ends
-- statement:
--   The DWalk construction uses the sep ends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Dual.lean#L157-L162
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Dual.lean#L157-L162

import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Dual
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge}

theorem ULHC.DWalk.sep_ends (hs : Solid V) (hFV : Inside V F) (x0 : Pt)
    (hconn : ∀ z ∈ V, Conn (GE V) x0 z) {a : Pt} {B : Finset Edge} (h : DWalk V F a a B)
    {e : Edge} {u v : Pt} (hE : Ends e u v) (he : e ∈ B) (hu : u ∈ V) (hv : v ∈ V) :
    ¬ Conn F u v := by sorry
