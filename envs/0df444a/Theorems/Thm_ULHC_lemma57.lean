-- Prove2me | Theorems.Thm_ULHC_lemma57
-- name    : ULHC.lemma57
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:43:53.634184+00:00
-- url     : https://prove2.me/theorems/0cbd7f3e-4876-4c44-aa6e-934a02a6ff87
-- title:
--   ULHC: lemma57
-- statement:
--   The ULHC construction uses the lemma57 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L687-L715
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L687-L715

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
include hF hT hk hcell hpat hsep

theorem ULHC.lemma57 (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z) {d : Pt}
    (hd : IsCell V d) (hd3 : ¬ NotTypeIII V (flipCol F c s (k + 2)) d) :
    ∃ d' ∈ chainCells V (flipCol F c s (k + 2)) (cellJ c s (k + 1)),
      ¬ NotTypeIII V (flipCol F c s (k + 2)) d' := by sorry
