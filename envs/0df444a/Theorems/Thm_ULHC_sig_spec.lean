-- Prove2me | Theorems.Thm_ULHC_sig_spec
-- name    : ULHC.sig_spec
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:48:09.471813+00:00
-- url     : https://prove2.me/theorems/2c7300a6-a550-463c-9bc8-1ff6662ba9e3
-- title:
--   ULHC: sig spec
-- statement:
--   The ULHC construction uses the sig spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Phase.lean#L81-L84
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Phase.lean#L81-L84

import Definitions.Def_ULHC_Walk
import Definitions.Def_ULHC_Phase
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F H : Finset Edge} {P : Finset Pt}
  (hF : Deg2 V F) (hH : Deg2 V H) (hs : Solid V) (hB : Border V F P) (hT : NoTypeIII V F)
  (o : Bool)

theorem ULHC.sig_spec {w : Pt} (h : Out F P o w) :
    ∃ so, sig F P o w = nb w so ∧ Cut P (sideEdge w so) ∧ outArc F w so = o := by sorry
