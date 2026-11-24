-- Prove2me | Theorems.Thm_ULHC_darkened_cell_notTypeIII
-- name    : ULHC.darkened_cell_notTypeIII
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:43:27.821828+00:00
-- url     : https://prove2.me/theorems/fdab7bf5-7f8c-49ec-a683-819369980a6b
-- title:
--   ULHC: darkened cell not Type III
-- statement:
--   The ULHC construction uses the darkened cell not Type III property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L452-L472
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L452-L472

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

theorem ULHC.darkened_cell_notTypeIII (hγ : lat1 (cellJ c s (k + 2)) s ∈ F) {d : Pt} {e : Edge}
    (he1 : e ∈ flipCol F c s (k + 2)) (he2 : e ∉ F) (hed : e ∈ cellE d) :
    NotTypeIII V (flipCol F c s (k + 2)) d := by sorry
