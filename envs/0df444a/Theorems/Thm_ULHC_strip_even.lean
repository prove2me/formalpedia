-- Prove2me | Theorems.Thm_ULHC_strip_even
-- name    : ULHC.strip_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:40:29.123872+00:00
-- url     : https://prove2.me/theorems/8977897b-b9de-41f0-82d1-84a022cf6388
-- title:
--   ULHC: strip even
-- statement:
--   The ULHC construction uses the strip even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L560-L591
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L560-L591

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {c : Pt} {s : Side}

theorem ULHC.strip_even (k : ℕ) (hk : k % 2 = 0) (F : Finset Edge) (hF : Deg2 V F)
    (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
    (hsep : ¬ Conn F (back1 c s) (front1 c s))
    (hsame : Conn F (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s)) :
    ncomp V (flipCol F c s (k + 2)) = ncomp V F := by sorry
