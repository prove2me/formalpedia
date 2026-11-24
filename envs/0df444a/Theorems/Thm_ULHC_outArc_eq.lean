-- Prove2me | Theorems.Thm_ULHC_outArc_eq
-- name    : ULHC.outArc_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:38:04.021615+00:00
-- url     : https://prove2.me/theorems/285293a6-6fdf-4749-a091-fffe76471499
-- title:
--   ULHC: out Arc eq
-- statement:
--   The ULHC construction uses the out Arc eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Arcs.lean#L107-L127
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Arcs.lean#L107-L127

import Definitions.Def_ULHC_Potential
import Definitions.Def_ULHC_Arcs
set_option autoImplicit true
open ULHC

theorem ULHC.outArc_eq (F : Finset Edge) (c : Pt) (s : Side) :
    outArc F c s =
      if s.horiz then (par c == decide (sideEdge c s ∈ F))
      else !(par c == decide (sideEdge c s ∈ F)) := by sorry
