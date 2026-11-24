-- Prove2me | Theorems.Thm_ULHC_even_end_border
-- name    : ULHC.even_end_border
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:38:22.807292+00:00
-- url     : https://prove2.me/theorems/c98b9303-9057-4161-aace-ad5549e9ea01
-- title:
--   ULHC: even end border
-- statement:
--   The ULHC construction uses the even end border property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/V2.lean#L124-L139
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/V2.lean#L124-L139

import Definitions.Def_ULHC_TheoremA
import Definitions.Def_ULHC_V2
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {c : Pt} {s : Side}

theorem ULHC.even_end_border (k : ℕ) (hk : k % 2 = 0) (F : Finset Edge) (hF : Deg2 V F)
    (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
    (hsep : ¬ Conn F (back1 c s) (front1 c s))
    (hsame : Conn F (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s)) :
    ¬ Conn (flipCol F c s (k + 2)) (back1 (cellJ c s (k + 1)) s) (front1 (cellJ c s (k + 1)) s) := by sorry
