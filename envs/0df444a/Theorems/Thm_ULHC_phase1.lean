-- Prove2me | Theorems.Thm_ULHC_phase1
-- name    : ULHC.phase1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:41:36.351524+00:00
-- url     : https://prove2.me/theorems/8dff2850-5642-4850-8da3-c02b06fdcc6e
-- title:
--   ULHC: phase1
-- statement:
--   The ULHC construction uses the phase1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Phase.lean#L123-L217
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Phase.lean#L123-L217

import Definitions.Def_ULHC_Walk
import Definitions.Def_ULHC_Phase
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F H : Finset Edge} {P : Finset Pt}
  (hF : Deg2 V F) (hH : Deg2 V H) (hs : Solid V) (hB : Border V F P) (hT : NoTypeIII V F)
  (o : Bool)
include hF hH hs hB hT

theorem ULHC.phase1 (v : Pt) (s0 : Side) (hcut : Cut P (sideEdge v s0)) (hin : outArc F v s0 = !o)
    (hjump : if o then D F H v = D F H (nb v s0) + 2 else D F H v = D F H (nb v s0) - 2)
    (hgood : Good o (D F H v)) :
    ∃ w, IsCell V w ∧ Good o (D F H w) ∧ Stop F P o w := by sorry
