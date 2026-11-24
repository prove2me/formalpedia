-- Prove2me | Theorems.Thm_ULHC_beyond_not_alt
-- name    : ULHC.beyond_not_alt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:42:54.312538+00:00
-- url     : https://prove2.me/theorems/52447032-be95-4a5c-8fdb-f8addba58575
-- title:
--   ULHC: beyond not alt
-- statement:
--   The ULHC construction uses the beyond not alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L394-L403
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L394-L403

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

theorem ULHC.beyond_not_alt (h1 : lat1 (cellJ c s (k + 2)) s ∈ F) :
    ¬ Alt (flipCol F c s (k + 2)) (cellJ c s (k + 2)) := by sorry
