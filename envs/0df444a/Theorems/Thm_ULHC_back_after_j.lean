-- Prove2me | Theorems.Thm_ULHC_back_after_j
-- name    : ULHC.back_after_j
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:39:13.059012+00:00
-- url     : https://prove2.me/theorems/ad971a45-3b81-45e9-8129-8a1446db24b6
-- title:
--   ULHC: back after j
-- statement:
--   The ULHC construction uses the back after j property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L164-L167
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L164-L167

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hk : k % 2 = 0) (hpat : StripPat F c s (k + 2))
include hk hpat

theorem ULHC.back_after_j {j : ℕ} (hj : 1 ≤ j) (hj' : j ≤ k + 1) :
    back (cellJ c s j) s ∈ flipCol F c s (k + 2) ↔ j % 2 = 0 := by sorry
