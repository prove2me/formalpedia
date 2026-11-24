-- Prove2me | Theorems.Thm_ULHC_corners_of_side
-- name    : ULHC.corners_of_side
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:41:07.7298+00:00
-- url     : https://prove2.me/theorems/e195a866-b1e2-4e26-a830-7d4f66b30dd8
-- title:
--   ULHC: corners of side
-- statement:
--   The ULHC construction uses the corners of side property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Walk.lean#L232-L238
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Walk.lean#L232-L238

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_Walk
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.corners_of_side (c : Pt) (s : Side) (P : Finset Pt)
    (h : (c ∈ P ↔ (c.1 + 1, c.2) ∈ P) ∧ (c ∈ P ↔ (c.1, c.2 + 1) ∈ P) ∧
      (c ∈ P ↔ (c.1 + 1, c.2 + 1) ∈ P)) : ¬ Cut P (sideEdge c s) := by sorry
