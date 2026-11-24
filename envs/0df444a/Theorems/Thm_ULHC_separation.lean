-- Prove2me | Theorems.Thm_ULHC_separation
-- name    : ULHC.separation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:32:41.577386+00:00
-- url     : https://prove2.me/theorems/3b0f8ca4-7475-4696-9eb6-316601f4825f
-- title:
--   ULHC: separation
-- statement:
--   The ULHC construction uses the separation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L643-L691
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L643-L691

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} (B : Finset Edge)
variable (hs : Solid V) (heven : ∀ c, IsCell V c → sidesIn B c % 2 = 0)
include hs heven

theorem ULHC.separation {F : Finset Edge} (hFV : Inside V F) (hBF : ∀ e ∈ B, e ∉ F)
    (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z) :
    ∃ P : Finset Pt, Border V F P ∧ ∀ e, IsEdge V e → (Cut P e ↔ e ∈ B) := by sorry
