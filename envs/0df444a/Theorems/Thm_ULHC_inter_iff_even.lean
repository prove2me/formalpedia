-- Prove2me | Theorems.Thm_ULHC_inter_iff_even
-- name    : ULHC.inter_iff_even
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:45:39.592884+00:00
-- url     : https://prove2.me/theorems/438791b4-6d86-4082-be54-474d1a50f1e2
-- title:
--   ULHC: inter iff even
-- statement:
--   The ULHC construction uses the inter iff even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Dual.lean#L180-L203
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Dual.lean#L180-L203

import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Dual
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge}

theorem ULHC.inter_iff_even (hs : Solid V) (hFV : Inside V F) (x0 : Pt)
    (hconn : ∀ z ∈ V, Conn (GE V) x0 z) {e : Edge} (hE : IsEdge V e) :
    ¬ Conn F e.p e.q ↔ ∃ B : Finset Edge, (∀ c, IsCell V c → sidesIn B c % 2 = 0) ∧
      (∀ f ∈ B, f ∉ F) ∧ e ∈ B := by sorry
