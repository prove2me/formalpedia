-- Prove2me | Theorems.Thm_ULHC_darkened
-- name    : ULHC.darkened
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:43:14.696809+00:00
-- url     : https://prove2.me/theorems/74c59e63-8f41-4d15-bc02-26fa7ff4b8c9
-- title:
--   ULHC: darkened
-- statement:
--   The ULHC construction uses the darkened property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L408-L446
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L408-L446

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
include hk hpat

theorem ULHC.darkened {e : Edge} (h1 : e ∈ flipCol F c s (k + 2)) (h2 : e ∉ F) :
    (∃ j ≤ k, j % 2 = 0 ∧ (e = lat1 (cellJ c s j) s ∨ e = lat2 (cellJ c s j) s)) ∨
      e = front (cellJ c s (k + 1)) s := by sorry
