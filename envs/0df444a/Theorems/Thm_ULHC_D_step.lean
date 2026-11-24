-- Prove2me | Theorems.Thm_ULHC_D_step
-- name    : ULHC.D_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:55:35.801703+00:00
-- url     : https://prove2.me/theorems/d823d8cb-bbf8-4af9-943f-d41119ecbc2c
-- title:
--   ULHC: D step
-- statement:
--   The ULHC construction uses the D step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/D.lean#L108-L130
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/D.lean#L108-L130

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge}
  (hF : IsFactor V d F) (hH : IsFactor V d H)
include hF hH

theorem ULHC.D_step (c : Pt) (s : Side) :
    (if outArc F c s then D F H (nb c s) - D F H c else D F H c - D F H (nb c s)) =
      if (decide (sideEdge c s ∈ F) ^^ decide (sideEdge c s ∈ H)) then 2 else 0 := by sorry
