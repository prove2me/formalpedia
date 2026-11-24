-- Prove2me | Theorems.Thm_ULHC_lat2_after
-- name    : ULHC.lat2_after
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:27:57.828496+00:00
-- url     : https://prove2.me/theorems/824ce251-60d5-4ee2-aa4b-d5456b97935a
-- title:
--   ULHC: lat2 after
-- statement:
--   The ULHC construction uses the lat2 after property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L147-L149
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L147-L149

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hk : k % 2 = 0) (hpat : StripPat F c s (k + 2))
include hk hpat

theorem ULHC.lat2_after {j : ℕ} (hj : j ≤ k + 1) :
    lat2 (cellJ c s j) s ∈ flipCol F c s (k + 2) ↔ j % 2 = 0 := by sorry
