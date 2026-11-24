-- Prove2me | Theorems.Thm_ULHC_phase2
-- name    : ULHC.phase2
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:41:53.817916+00:00
-- url     : https://prove2.me/theorems/a3706647-d6ba-4b93-8942-d1929f3ae2b2
-- title:
--   ULHC: phase2
-- statement:
--   The ULHC construction uses the phase2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Phase2.lean#L271-L333
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Phase2.lean#L271-L333

import Definitions.Def_ULHC_Phase
import Definitions.Def_ULHC_Phase2
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F H : Finset Edge} {P : Finset Pt}
  (hF : Deg2 V F) (hH : Deg2 V H) (hs : Solid V) (hB : Border V F P)
include hF hH hs hB

theorem ULHC.phase2 {w : Pt} {o : Bool} (hg : Good o (D F H w)) (hst : Stop F P o w) :
    ∃ s n, 2 ≤ n ∧ StripPat F w s n ∧ (∀ j < n, IsCell V (cellJ w s j)) ∧
      (∀ j < n, Good o (D F H (cellJ w s j))) ∧ ParOK w s o ∧
      ¬ Conn F (back1 w s) (front1 w s) := by sorry
