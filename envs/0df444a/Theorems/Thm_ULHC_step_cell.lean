-- Prove2me | Theorems.Thm_ULHC_step_cell
-- name    : ULHC.step_cell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:40:47.805174+00:00
-- url     : https://prove2.me/theorems/5e746ced-1260-4237-8592-af8b51196180
-- title:
--   ULHC: step cell
-- statement:
--   The ULHC construction uses the step cell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Walk.lean#L129-L190
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Walk.lean#L129-L190

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_Walk
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.step_cell {V : Finset Pt} {F : Finset Edge} {P : Finset Pt} (hB : Border V F P)
    (w : Pt) (o : Bool)
    (hlat : ∀ s, Cut P (sideEdge w s) → sideEdge w (latA s) ∈ F ∨ sideEdge w (latB s) ∈ F)
    (halt : Alt F w → ∀ s, ¬ Cut P (sideEdge w s))
    (si : Side) (hcut : Cut P (sideEdge w si)) (hin : outArc F w si = !o) :
    (∃ so, so ≠ si ∧ Cut P (sideEdge w so) ∧ outArc F w so = o ∧
        ∀ s', Cut P (sideEdge w s') → outArc F w s' = !o → s' = si) ∨
    (∃ d, sideEdge w d ∈ F ∧ sideEdge w d.opp ∉ F ∧ sideEdge w (latA d) ∉ F ∧
        sideEdge w (latB d) ∉ F ∧ (si = latA d ∨ si = latB d) ∧ ¬ Cut P (sideEdge w d.opp) ∧
        outArc F w d.opp = o ∧ ∀ s, Cut P (sideEdge w s) → outArc F w s = !o) := by sorry
