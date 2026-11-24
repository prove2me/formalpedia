-- Prove2me | Theorems.Thm_ULHC_end_inter
-- name    : ULHC.end_inter
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:39:31.189458+00:00
-- url     : https://prove2.me/theorems/56c3986e-25de-4496-8614-6500fd3f0045
-- title:
--   ULHC: end inter
-- statement:
--   The ULHC construction uses the end inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L592-L607
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L592-L607

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

theorem ULHC.end_inter :
    Inter V (flipCol F c s (k + 2)) (lat1 (cellJ c s (k + 1)) s) ∧
      lat1 (cellJ c s (k + 1)) s ∈
        EB V (flipCol F c s (k + 2)) (cellJ c s (k + 1)) := by sorry
