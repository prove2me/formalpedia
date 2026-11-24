-- Prove2me | Theorems.Thm_ULHC_back_after
-- name    : ULHC.back_after
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:39:10.00923+00:00
-- url     : https://prove2.me/theorems/ca127c8d-f67d-4d22-813e-7f8c6714befd
-- title:
--   ULHC: back after
-- statement:
--   The ULHC construction uses the back after property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L161-L162
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L161-L162

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hk : k % 2 = 0) (hpat : StripPat F c s (k + 2))
include hk hpat

theorem ULHC.back_after : back c s ∉ flipCol F c s (k + 2) := by sorry
