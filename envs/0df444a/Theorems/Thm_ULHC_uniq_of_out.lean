-- Prove2me | Theorems.Thm_ULHC_uniq_of_out
-- name    : ULHC.uniq_of_out
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:48:12.330799+00:00
-- url     : https://prove2.me/theorems/ff2a0de5-36cd-49bc-890e-74f24100df71
-- title:
--   ULHC: uniq of out
-- statement:
--   The ULHC construction uses the uniq of out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Phase.lean#L97-L108
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Phase.lean#L97-L108

import Definitions.Def_ULHC_Walk
import Definitions.Def_ULHC_Phase
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F H : Finset Edge} {P : Finset Pt}
  (hF : Deg2 V F) (hH : Deg2 V H) (hs : Solid V) (hB : Border V F P) (hT : NoTypeIII V F)
  (o : Bool)
include hF hB hT

theorem ULHC.uniq_of_out {w : Pt} (hw : IsCell V w) (si : Side) (hcut : Cut P (sideEdge w si))
    (hin : outArc F w si = !o) (hout : Out F P o w) :
    ∀ s1 s2, Cut P (sideEdge w s1) → outArc F w s1 = !o →
      Cut P (sideEdge w s2) → outArc F w s2 = !o → s1 = s2 := by sorry
