-- Prove2me | Theorems.Thm_ULHC_alpha_typeIII
-- name    : ULHC.alpha_typeIII
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:43:40.589288+00:00
-- url     : https://prove2.me/theorems/ade69307-3c58-456e-bcfb-c7cbe0896d80
-- title:
--   ULHC: alpha type III
-- statement:
--   The ULHC construction uses the alpha type III property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L613-L681
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L613-L681

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

theorem ULHC.alpha_typeIII (hα : lat1 (cellJ c s (k + 2)) s ∉ F) :
    nb (cellJ c s (k + 1)) (latA s) ∈ chainCells V (flipCol F c s (k + 2)) (cellJ c s (k + 1)) ∧
      ¬ NotTypeIII V (flipCol F c s (k + 2)) (nb (cellJ c s (k + 1)) (latA s)) := by sorry
